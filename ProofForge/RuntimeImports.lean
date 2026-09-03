import Lean

/-!
Runtime import support for executables that re-extract user modules
(`pf build`, golden test drivers).

Lean's module lookup (`System.SearchPath.findWithExt`) short-circuits on the
first search-path entry whose module-root *directory* exists. With a
multi-package workspace (each package owning files under the same
`ProofForge/` root directory) the first entry therefore shadows modules that
only exist in later entries — e.g. `ProofForge.Attr` lives in
`proofforge-common` while `ProofForge.olean` (umbrella) lives in the target
repo.

`mergedSearchPath` resolves the transitive import closure of the requested
modules by file existence (via each module's `.ilean` `directImports`),
materializes a merged view of the resolved artifacts in a temp directory, and
returns that directory followed by the original search path. Pointing the
search path at the merged view first makes every needed module resolvable
from a single directory.
-/

namespace ProofForge.RuntimeImports

/-- Read a module's direct imports from its `.ilean` sidecar (JSON). Returns
    `[]` when the sidecar is missing or unreadable; importModules will surface
    any real resolution problem for those imports. -/
private def directImports? (ilean : System.FilePath) : IO (Array Lean.Name) := do
  let contents ← IO.FS.readFile ilean
  match Lean.Json.parse contents with
  | .error _ => pure #[]
  | .ok json =>
    match json.getObjVal? "directImports" with
    | .error _ => pure #[]
    | .ok imports =>
      let entries : Array Lean.Json :=
        match imports.getArr? with
        | .ok arr => arr
        | .error _ => #[]
      let mut names : Array Lean.Name := #[]
      for entry in entries do
        let first? : Option Lean.Json :=
          match entry.getArr? with
          | .ok arr => arr[0]?
          | .error _ => none
        match first? with
        | some (Lean.Json.str name) => names := names.push name.toName
        | _ => pure ()
      pure names

/-- All search-path entries: `LEAN_PATH` after the initialized default. -/
private def allDirs : IO (List System.FilePath) := do
  let mut dirs := (← Lean.searchPathRef.get)
  if let some sp := ← IO.getEnv "LEAN_PATH" then
    for p in sp.splitOn ":" do
      if p.isEmpty then continue
      try dirs := dirs ++ [← IO.FS.realPath p] catch _ => pure ()
  pure dirs

variable [Inhabited System.FilePath]

/-- Resolve the transitive import closure of `rootModules` file-existence-first
    across the current search path plus `LEAN_PATH`, then set the search path
    to a merged view that resolves every module. Falls back to the plain
    search path when the closure is incomplete. -/
public def mergedSearchPath (rootModules : Array Lean.Name) : IO Unit := do
  let dirs₀ ← allDirs
  let mut visited : Std.HashSet Lean.Name := {}
  let mut queue : Array Lean.Name := rootModules
  let mut missing : Array Lean.Name := #[]
  -- module → (olean, sidecars) real paths
  let mut artifacts : Array (Lean.Name × System.FilePath × Array System.FilePath) := #[]
  repeat
    if queue.isEmpty then break
    let mod := queue[0]!
    queue := queue.drop 1
    if visited.contains mod then continue
    visited := visited.insert mod
    let mut found : Option System.FilePath := none
    for dir in dirs₀ do
      let olean := Lean.modToFilePath dir mod "olean"
      if ← olean.pathExists then
        found := some olean
        break
    match found with
    | none => missing := missing.push mod
    | some olean =>
        let sidecars := ["ilean", "olean.private", "olean.server", "ir"]
          |>.map (System.FilePath.withExtension olean ·)
          |>.filter (fun p => p.toString != olean.toString)
        let mut present : Array System.FilePath := #[]
        for sc in sidecars do
          if ← sc.pathExists then present := present.push sc
        artifacts := artifacts.push (mod, olean, present)
        let imports ← directImports? (System.FilePath.withExtension olean "ilean")
        for name in imports do
          queue := queue.push name
  if missing.isEmpty && !artifacts.isEmpty then
    let mergeDir : System.FilePath :=
      ((← IO.getEnv "XDG_RUNTIME_DIR") |>.getD ((← IO.getEnv "TMPDIR") |>.getD "/tmp"))
        / "pf-lean-merged"
    for (mod, olean, sidecars) in artifacts do
      let dst := Lean.modToFilePath mergeDir mod "olean"
      if !(← dst.parent.get!.pathExists) then
        IO.FS.createDirAll dst.parent.get!
      IO.FS.writeBinFile dst (← IO.FS.readBinFile olean)
      for sc in sidecars do
        let dstSide := System.FilePath.withExtension dst (sc.extension.getD "ilean")
        IO.FS.writeBinFile dstSide (← IO.FS.readBinFile sc)
    Lean.searchPathRef.set (mergeDir :: dirs₀)
  else
    Lean.searchPathRef.set dirs₀

end ProofForge.RuntimeImports