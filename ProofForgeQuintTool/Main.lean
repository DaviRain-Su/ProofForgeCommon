import ProofForge.Quint.Emit
import ProofForgeCoreTests.QuintFixtures

/-!
`quintEmit` executable: compiles every shared Quint fixture program and writes
it as a `.qnt` module. The CI Quint CLI gate parses and typechecks the emitted
files with the real Quint toolchain.

Usage: `quintEmit [output-dir]` (default `.lake/build/quint`).
-/

open ProofForge

namespace ProofForgeQuintTool.Main

private def emitTo (dir : System.FilePath)
    (program : Core.IR.Program Quint.Ops.ValKind Quint.Ops.OpExt) : IO Unit := do
  match Quint.Emit.compileProgram program with
  | .ok text =>
      let path := dir / s!"{program.name}.qnt"
      IO.FS.writeFile path text
      IO.println s!"wrote {path}"
  | .error reason =>
      throw <| IO.userError s!"quint/emit: {program.name}: {reason}"

end ProofForgeQuintTool.Main

def main (args : List String) : IO Unit := do
  let dir : System.FilePath := ⟨args.head?.getD ".lake/build/quint"⟩
  IO.FS.createDirAll dir
  for program in ProofForgeCoreTests.QuintFixtures.all do
    ProofForgeQuintTool.Main.emitTo dir program
