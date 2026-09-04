import ProofForge.Quint.Registration
import ProofForge.Core.IR

/-!
# ProofForge.Quint.Emit — Core IR → Quint (`.qnt`) source

Default-target backend: lowers an extension-free `Core.IR.Program` to a
source-only Quint module. Semantics follow the proof_forge Quint Q0 target:

- one `var pf_state_<leaf>: int` per program slot; UInt64 values are unsigned
  Quint `int`s in `0..PF_MAX_U64`;
- `action init`: parameters are `nondet … = oneOf(0.to(PF_MAX_U64))`; the init
  method is exactly one `returnState` per slot in declaration order. A program
  without an init method gets a synthetic all-zero init;
- `action step = any { … }`: one branch per `increment` method. Parameters are
  nondet over the full UInt64 domain. Checked arithmetic statements compile to
  exact success conditions on unbounded ints (`l + r <= PF_MAX_U64`, `l >= r`,
  `r != 0`); a failed branch stutters business state and records the
  first-failure code in `pf_last_failure`;
- `get` methods become `pure def pf_view_<name>`;
- instrumentation: `pf_last_action`, `pf_last_ok`, `pf_last_failure`, plus
  per-entry `pf_last_<name>_arg<i>` / `pf_last_<name>_result`;
- implicit writeback mirrors `Core.evaluate`: a store-free arm whose first
  checked statement reads a state leaf commits the checked result to that
  leaf (otherwise to the first leaf).

Fail closed (outside the default subset): bitwise/shift values, vector index
reads/writes, loops (`forAccum`/`forBody`), `setLocal`/`joinLocal`, typed
errors, events, external calls, non-8-byte slots, and any `ext` leaf (the
dialect has none).

No Quint CLI, Apalache, TLC, or JVM is invoked; the emitted source carries no
parse/typecheck/run/verify evidence.
-/

namespace ProofForge.Quint.Emit

open ProofForge.Core

private abbrev CVal := Core.Ops.Val Ops.ValKind
private abbrev COp := Core.Ops.Op Ops.ValKind Ops.OpExt

private def emitError (message : String) : Except String α :=
  .error s!"quint/emit: {message}"

-- ---------------------------------------------------------------------------
-- Structured Quint IR AST
-- ---------------------------------------------------------------------------

inductive QBinOp where
  | add | sub | mul | div | mod
  | eq | ne | lt | le | gt | ge
  | and | or
  deriving BEq, Inhabited, Repr

inductive QExpr where
  | name (id : String)
  | intLit (value : String)
  | boolLit (value : Bool)
  | binary (op : QBinOp) (lhs rhs : QExpr)
  | not (operand : QExpr)
  | call (callee : String) (args : Array QExpr)
  | ifThenElse (cond thenE elseE : QExpr)
  deriving BEq, Inhabited, Repr

/-- One nondet binding (`nondet x = oneOf(...)`). -/
structure QNondetBind where
  name : String
  domain : QExpr
  deriving BEq, Repr

/-- One local value binding inside an action branch (`val x = e`). -/
structure QPureBind where
  name : String
  value : QExpr
  deriving BEq, Repr

/-- Assignment in `all { x' = e, ... }`. -/
structure QAssign where
  target : String
  value : QExpr
  deriving BEq, Repr

/-- One action branch (init body or one `step` alternative). -/
structure QActionBranch where
  nondets : Array QNondetBind := #[]
  pures : Array QPureBind := #[]
  assigns : Array QAssign := #[]
  deriving BEq, Inhabited, Repr

inductive QDecl where
  /-- `pure def PF_MAX_U64: int = ...` -/
  | pureConst (name : String) (ty : String) (value : QExpr)
  /-- `var name: ty` -/
  | varDecl (name : String) (ty : String)
  /-- `pure def name(params): ty = body`, nullary when `params` is empty -/
  | pureDef (name : String) (params : Array (String × String)) (retTy : String)
      (body : QExpr)
  /-- `action init = { ... }` single branch -/
  | actionInit (branch : QActionBranch)
  /-- `action step = any { ... }` -/
  | actionStep (branches : Array QActionBranch)
  deriving BEq, Repr

structure QModule where
  name : String
  headerComment : String
  decls : Array QDecl
  deriving BEq, Repr

-- ---------------------------------------------------------------------------
-- Limits and identifiers
-- ---------------------------------------------------------------------------

private def maxSlots : Nat := 64
private def maxMethods : Nat := 256
private def maxParams : Nat := 64
private def maxChecks : Nat := 128
private def maxStores : Nat := 64
private def maxLocals : Nat := 256
private def maxExprDepth : Nat := 256
private def maxExprNodes : Nat := 16384
private def maxIdentChars : Nat := 200

/-- ASCII identifier safe to splice after a `pf_…` / `PFModel_` prefix. -/
private def isIdent (name : String) : Bool :=
  !name.isEmpty && name.length ≤ maxIdentChars &&
    (name.front.isAlpha || name.front == '_') &&
    name.all fun c => c.toNat < 128 && (c.isAlphanum || c == '_')

-- ---------------------------------------------------------------------------
-- Failure codes and target-owned names
-- ---------------------------------------------------------------------------

/-- First-failure instrumentation codes (same table as the Q0 target). -/
private def failureCodeOverflow : Nat := 1
private def failureCodeUnderflow : Nat := 2
private def failureCodeDivByZero : Nat := 3

/-- Declared reverts (`errorNamed`) keep source identity via
    `256 + first-appearance index`. -/
private def declaredRevertCode (index : Nat) : Nat := 256 + index

private def moduleNameOf (programName : String) : String :=
  "PFModel_" ++ programName

private def stateName (leaf : String) : String := "pf_state_" ++ leaf
private def viewName (method : String) : String := "pf_view_" ++ method

private def entryParamName (actionIndex paramIndex : Nat) : String :=
  s!"pf_arg_a{actionIndex}_{paramIndex}"

private def initParamName (paramIndex : Nat) : String := s!"pf_init_arg{paramIndex}"

private def viewParamName (viewIndex paramIndex : Nat) : String :=
  s!"pf_view_arg_{viewIndex}_{paramIndex}"

private def lastArgName (entry : String) (i : Nat) : String :=
  s!"pf_last_{entry}_arg{i}"

private def lastResultName (entry : String) : String := s!"pf_last_{entry}_result"

private def maxU64Lit : String := "18446744073709551615"

private def pfMaxRef : QExpr := .name "PF_MAX_U64"

/-- Full UInt64 nondet domain: `oneOf(0.to(PF_MAX_U64))`. -/
private def u64Domain : QExpr :=
  .call "oneOf" #[.call "to" #[.intLit "0", pfMaxRef]]

-- ---------------------------------------------------------------------------
-- Expression budget
-- ---------------------------------------------------------------------------

private partial def qDepth : QExpr → Nat
  | .name _ | .intLit _ | .boolLit _ => 1
  | .not x => qDepth x + 1
  | .binary _ l r => max (qDepth l) (qDepth r) + 1
  | .call _ args => (args.foldl (init := 0) fun m a => max m (qDepth a)) + 1
  | .ifThenElse c t e => max (qDepth c) (max (qDepth t) (qDepth e)) + 1

/-- Node count capped at `budget + 1` so oversized trees bail early. -/
private partial def qCount (budget : Nat) (stack : Array QExpr) (count : Nat) : Nat :=
  if count > budget then count
  else
    match stack.back? with
    | none => count
    | some cur =>
        let rest := stack.pop
        match cur with
        | .name _ | .intLit _ | .boolLit _ => qCount budget rest (count + 1)
        | .not x => qCount budget (rest.push x) (count + 1)
        | .binary _ l r => qCount budget (rest.push l |>.push r) (count + 1)
        | .call _ args => qCount budget (rest ++ args) (count + 1)
        | .ifThenElse c t e => qCount budget (rest.push c |>.push t |>.push e) (count + 1)

private def validateExpr (e : QExpr) : Except String Unit := do
  if qDepth e > maxExprDepth then
    emitError "expression exceeds the emission depth budget"
  else if qCount maxExprNodes #[e] 0 > maxExprNodes then
    emitError "expression exceeds the emission node budget"

-- ---------------------------------------------------------------------------
-- Core value lowering
-- ---------------------------------------------------------------------------

private structure LowerCtx where
  slots : Array String
  params : Array String
  declaredErrors : Array String := #[]
  locals : Array (Option QExpr) := #[]

private def LowerCtx.bindLocal (ctx : LowerCtx) (i : Nat) (value : QExpr) :
    Except String LowerCtx := do
  unless i < maxLocals do
    emitError s!"local index {i} exceeds the local limit"
  let grown :=
    if ctx.locals.size ≤ i then
      ctx.locals ++ Array.replicate (i + 1 - ctx.locals.size) none
    else ctx.locals
  pure { ctx with locals := grown.set! i (some value) }

private def cmpOp : Core.Ops.Cmp → QBinOp
  | .eq => .eq | .ne => .ne | .lt => .lt | .le => .le | .gt => .gt | .ge => .ge

private def firstLeaf (ctx : LowerCtx) : Except String String :=
  match ctx.slots[0]? with
  | some n => pure n
  | none => emitError "program has no state slots"

/-- Render a Core value as a Quint expression. State reads resolve by leaf
    name against the flat slot table; the field base is ignored. -/
private partial def lowerVal (ctx : LowerCtx) : CVal → Except String QExpr
  | .arg i =>
      match ctx.params[i]? with
      | some n => pure (.name n)
      | none => emitError s!"parameter index {i} out of range"
  | .local i =>
      match ctx.locals[i]? with
      | some (some e) => pure e
      | _ => emitError s!"unbound local {i}"
  | .field _ name =>
      if ctx.slots.contains name then pure (.name (stateName name))
      else emitError s!"unknown state leaf '{name}'"
  | .lit n => pure (.intLit (toString n.toNat))
  | .addU64 l r => return .binary .add (← lowerVal ctx l) (← lowerVal ctx r)
  | .subU64 l r => return .binary .sub (← lowerVal ctx l) (← lowerVal ctx r)
  | .mulU64 l r => return .binary .mul (← lowerVal ctx l) (← lowerVal ctx r)
  | .divU64 l r => do
      let ql ← lowerVal ctx l
      let qr ← lowerVal ctx r
      -- Guard div by zero so failed actions still evaluate.
      pure (.ifThenElse (.binary .ne qr (.intLit "0")) (.binary .div ql qr) (.intLit "0"))
  | .modU64 l r => do
      let ql ← lowerVal ctx l
      let qr ← lowerVal ctx r
      pure (.ifThenElse (.binary .ne qr (.intLit "0")) (.binary .mod ql qr) (.intLit "0"))
  | .select cmp l r t e =>
      return .ifThenElse
        (.binary (cmpOp cmp) (← lowerVal ctx l) (← lowerVal ctx r))
        (← lowerVal ctx t) (← lowerVal ctx e)
  | .bitAnd .. | .bitOr .. | .bitXor .. | .bitNot .. | .shiftL .. | .shiftR .. =>
      emitError "bitwise/shift values are outside the Quint default-target subset"
  | .indexGet .. =>
      emitError "vector index reads are outside the Quint default-target subset"
  | .loopIx =>
      emitError "loops are outside the Quint default-target subset"
  | .ext kind _ => kind.elim (motive := fun _ => Except String QExpr)

-- ---------------------------------------------------------------------------
-- Method-body flattening
-- ---------------------------------------------------------------------------

private inductive CheckedKind where
  | add | sub | mul | div | mod

/-- (failure code, success condition, result value) for one checked arithmetic
    statement. Quint ints are unbounded, so the conditions are exact. -/
private def checkedParts (ctx : LowerCtx) (kind : CheckedKind) (l r : CVal) :
    Except String (Nat × QExpr × QExpr) := do
  let ql ← lowerVal ctx l
  let qr ← lowerVal ctx r
  match kind with
  | .add =>
      pure (failureCodeOverflow,
        .binary .le (.binary .add ql qr) pfMaxRef, .binary .add ql qr)
  | .sub =>
      pure (failureCodeUnderflow, .binary .ge ql qr, .binary .sub ql qr)
  | .mul =>
      pure (failureCodeOverflow,
        .binary .le (.binary .mul ql qr) pfMaxRef, .binary .mul ql qr)
  | .div =>
      pure (failureCodeDivByZero, .binary .ne qr (.intLit "0"),
        .ifThenElse (.binary .ne qr (.intLit "0")) (.binary .div ql qr) (.intLit "0"))
  | .mod =>
      pure (failureCodeDivByZero, .binary .ne qr (.intLit "0"),
        .ifThenElse (.binary .ne qr (.intLit "0")) (.binary .mod ql qr) (.intLit "0"))

private def fieldName? : CVal → Option String
  | .field _ name => some name
  | _ => none

/-- A flattened straight-line method body: conditional-free store map plus the
    success conditions that guard it. -/
private structure FlatBody where
  /-- (leaf, post-state) writes; later writes replace earlier ones. -/
  stores : Array (String × QExpr) := #[]
  /-- (failure code, success condition) in source order. -/
  checks : Array (Nat × QExpr) := #[]
  /-- Committed result value, when a reachable `okState` produced one. -/
  result? : Option QExpr := none
  deriving Inhabited
/-- Merge a pre-branch prefix body with two arm bodies under `cond`.
    Untaken-arm checks rewrite to `true`, so first-failure order within the
    taken path is preserved; unwritten leaves fall back to the prefix store,
    then to the pre-state identity. -/
private def mergeFlat (selfResult : String) (pre : FlatBody)
    (cond : QExpr) (t e : FlatBody) : FlatBody := Id.run do
  let lookup := fun (stores : Array (String × QExpr)) (leaf : String) =>
    stores.findSome? fun (n, v) => if n == leaf then some v else none
  let mut leaves : Array String := #[]
  for (n, _) in pre.stores ++ t.stores ++ e.stores do
    unless leaves.contains n do
      leaves := leaves.push n
  let mut stores : Array (String × QExpr) := #[]
  for leaf in leaves do
    let preState := QExpr.name (stateName leaf)
    let postT := (lookup t.stores leaf <|> lookup pre.stores leaf).getD preState
    let postE := (lookup e.stores leaf <|> lookup pre.stores leaf).getD preState
    stores := stores.push (leaf, .ifThenElse cond postT postE)
  let checks :=
    pre.checks ++
      t.checks.map (fun (c, ck) => (c, QExpr.ifThenElse cond ck (.boolLit true))) ++
      e.checks.map (fun (c, ck) => (c, QExpr.ifThenElse cond (.boolLit true) ck))
  let result? :=
    match t.result?, e.result? with
    | some rt, some re => some (.ifThenElse cond rt re)
    | some rt, none => some (.ifThenElse cond rt (.name selfResult))
    | none, some re => some (.ifThenElse cond (.name selfResult) re)
    | none, none => none
  { stores, checks, result? }

private def isErrorTerminal : COp → Bool
  | .errorOverflow | .errorNamed _ | .errorTyped _ => true
  | _ => false

/-- (new flat body, new first-checked) after pushing one checked arithmetic
    statement. The first checked statement of a store-free arm is remembered
    for the implicit writeback convention. -/
private def pushChecked (ctx : LowerCtx) (flat : FlatBody)
    (firstChecked? : Option (Option String × QExpr)) (kind : CheckedKind)
    (l r : CVal) :
    Except String (FlatBody × Option (Option String × QExpr)) := do
  let (code, cond, value) ← checkedParts ctx kind l r
  let nextFirst :=
    match firstChecked? with
    | some _ => firstChecked?
    | none => some (fieldName? l, value)
  pure ({ flat with checks := flat.checks.push (code, cond) }, nextFirst)

/-- Flatten a mutating method body. Every maximal straight-line segment must
    end in `okState` (commit) or an error terminal (revert); `ite` must be the
    last operation of its segment with self-contained arms. -/
private partial def compileMutateOps (ctx : LowerCtx) (selfResult : String)
    (flat : FlatBody) (firstChecked? : Option (Option String × QExpr))
    (ops : List COp) : Except String FlatBody := do
  match ops with
  | [] => emitError "method body must end in okState or an error terminal"
  | .letLocal i v :: rest =>
      let ctx ← ctx.bindLocal i (← lowerVal ctx v)
      compileMutateOps ctx selfResult flat firstChecked? rest
  | .setLocal .. :: _ | .joinLocal _ :: _ =>
      emitError "mutable or join locals are outside the Quint default-target subset"
  | .checkedAddU64 l r :: rest =>
      let (flat, firstChecked?) ← pushChecked ctx flat firstChecked? .add l r
      compileMutateOps ctx selfResult flat firstChecked? rest
  | .checkedSubU64 l r :: rest =>
      let (flat, firstChecked?) ← pushChecked ctx flat firstChecked? .sub l r
      compileMutateOps ctx selfResult flat firstChecked? rest
  | .checkedMulU64 l r :: rest =>
      let (flat, firstChecked?) ← pushChecked ctx flat firstChecked? .mul l r
      compileMutateOps ctx selfResult flat firstChecked? rest
  | .checkedDivU64 l r :: rest =>
      let (flat, firstChecked?) ← pushChecked ctx flat firstChecked? .div l r
      compileMutateOps ctx selfResult flat firstChecked? rest
  | .checkedModU64 l r :: rest =>
      let (flat, firstChecked?) ← pushChecked ctx flat firstChecked? .mod l r
      compileMutateOps ctx selfResult flat firstChecked? rest
  | .storeField n v :: rest => do
      unless ctx.slots.contains n do
        emitError s!"storeField targets unknown state leaf '{n}'"
      let q ← lowerVal ctx v
      let stores := (flat.stores.filter fun (m, _) => m != n).push (n, q)
      compileMutateOps ctx selfResult { flat with stores } firstChecked? rest
  | .okState v :: rest => do
      unless rest.all isErrorTerminal do
        emitError "only error terminals may trail an okState commit"
      if flat.stores.isEmpty then
        match firstChecked? with
        | some (leafName?, value) =>
            -- Implicit writeback, mirroring Core evaluation.
            let leaf ←
              match leafName? with
              | some n =>
                  if ctx.slots.contains n then pure n else firstLeaf ctx
              | none => firstLeaf ctx
            pure { flat with stores := #[(leaf, value)], result? := some value }
        | none =>
            pure { flat with result? := some (← lowerVal ctx v) }
      else
        pure { flat with result? := some (← lowerVal ctx v) }
  | .errorOverflow :: rest =>
      unless rest.all isErrorTerminal do
        emitError "operations follow revert"
      pure { flat with
        checks := flat.checks.push (failureCodeOverflow, .boolLit false) }
  | .errorNamed n :: rest =>
      unless rest.all isErrorTerminal do
        emitError "operations follow revert"
      match ctx.declaredErrors.idxOf? n with
      | some idx =>
          pure { flat with
            checks := flat.checks.push (declaredRevertCode idx, .boolLit false) }
      | none => emitError s!"undeclared error '{n}'"
  | .errorTyped _ :: _ =>
      emitError "typed errors are outside the Quint default-target subset"
  | .ite cmp l r thn els :: rest => do
      unless rest.isEmpty do
        emitError "if-then-else must be the last operation in its block"
      let qc := QExpr.binary (cmpOp cmp) (← lowerVal ctx l) (← lowerVal ctx r)
      let ft ← compileMutateOps ctx selfResult {} none thn.toList
      let fe ← compileMutateOps ctx selfResult {} none els.toList
      pure (mergeFlat selfResult flat qc ft fe)
  | .returnU64 _ :: _ | .returnState _ :: _ =>
      emitError "return operations are only admitted in view/init methods"
  | .forAccum .. :: _ | .forBody .. :: _ =>
      emitError "loops are outside the Quint default-target subset"
  | .indexSetLeaf .. :: _ | .indexSet .. :: _ =>
      emitError "vector writes are outside the Quint default-target subset"
  | .emitEvent .. :: _ =>
      emitError "events are outside the Quint default-target subset"
  | .externalCall .. :: _ =>
      emitError "external calls are outside the Quint default-target subset"
  | .ext payload :: _ => payload.elim (motive := fun _ => Except String FlatBody)
/-- Compile a view body to a single result expression. -/
private partial def compileViewOps (ctx : LowerCtx) (ops : List COp) :
    Except String QExpr := do
  match ops with
  | [] => emitError "view must end in returnU64"
  | .letLocal i v :: rest =>
      let ctx ← ctx.bindLocal i (← lowerVal ctx v)
      compileViewOps ctx rest
  | .returnU64 v :: rest => do
      unless rest.all isErrorTerminal do
        emitError "only error terminals may trail returnU64"
      lowerVal ctx v
  | .ite cmp l r thn els :: rest => do
      unless rest.isEmpty do
        emitError "if-then-else must be the last operation in its block"
      let qc := QExpr.binary (cmpOp cmp) (← lowerVal ctx l) (← lowerVal ctx r)
      let qt ← compileViewOps ctx thn.toList
      let qe ← compileViewOps ctx els.toList
      pure (.ifThenElse qc qt qe)
  | _ :: _ =>
      emitError "views must be side-effect free (no stores, checked arithmetic, or reverts)"

/-- Compile an init body: `letLocal` bindings followed by one `returnState`
    per slot, in declaration order. No fallible operations. -/
private partial def compileInitOps (ctx : LowerCtx) (values : Array QExpr)
    (ops : List COp) : Except String (Array QExpr) := do
  match ops with
  | [] =>
      if values.size == ctx.slots.size then pure values
      else
        emitError
          (s!"init must return exactly {ctx.slots.size} state values " ++
            "(one returnState per slot, in declaration order)")
  | .letLocal i v :: rest =>
      let ctx ← ctx.bindLocal i (← lowerVal ctx v)
      compileInitOps ctx values rest
  | .returnState v :: rest =>
      let q ← lowerVal ctx v
      compileInitOps ctx (values.push q) rest
  | _ :: _ =>
      emitError
        ("init admits only letLocal and returnState " ++
          "(no checks, stores, branches, or reverts)")

/-- Program-wide first-appearance order of `errorNamed` names (method order,
    then op order, then-arm before else-arm). -/
private partial def collectNamedErrors (ops : Array COp) (acc : Array String) :
    Array String :=
  ops.foldl (init := acc) fun acc op =>
    match op with
    | .errorNamed n => if acc.contains n then acc else acc.push n
    | .ite _ _ _ thn els => collectNamedErrors els (collectNamedErrors thn acc)
    | .forBody _ body => collectNamedErrors body acc
    | _ => acc

-- ---------------------------------------------------------------------------
-- Branch emission
-- ---------------------------------------------------------------------------

private structure EntryInfo where
  name : String
  paramCount : Nat

/-- First-failure pure cascade: `ck0..`, then `ok…` (and-chain), then `fail…`
    (reversed if-chain yielding the first failing code, else 0). -/
private def checkCascade (checks : Array (Nat × QExpr)) :
    Array QPureBind × String × String := Id.run do
  let mut pures : Array QPureBind := #[]
  for i in [0:checks.size] do
    pures := pures.push { name := s!"ck{i}", value := checks[i]!.2 }
  let okName := s!"ok{checks.size}"
  let successExpr : QExpr :=
    if checks.isEmpty then .boolLit true
    else Id.run do
      let mut acc : QExpr := .name "ck0"
      for i in [1:checks.size] do
        acc := .binary .and acc (.name s!"ck{i}")
      pure acc
  pures := pures.push { name := okName, value := successExpr }
  let failName := s!"fail{checks.size}"
  let failureExpr : QExpr := Id.run do
    let mut acc : QExpr := .intLit "0"
    let n := checks.size
    for i in [0:n] do
      let j := n - 1 - i
      acc := .ifThenElse (.not (.name s!"ck{j}"))
        (.intLit (toString checks[j]!.1)) acc
    pure acc
  pures := pures.push { name := failName, value := failureExpr }
  pure (pures, okName, failName)

private def emitEntryBranch (slots : Array String) (entries : Array EntryInfo)
    (declaredErrors : Array String) (method : Core.IR.Method Ops.ValKind Ops.OpExt)
    (actionIndex : Nat) : Except String QActionBranch := do
  unless method.paramCount ≤ maxParams do
    emitError s!"entry '{method.name}' parameter count exceeds limit"
  let selfResult := lastResultName method.name
  let mut emittedParams : Array String := #[]
  let mut nondets : Array QNondetBind := #[]
  for i in [0:method.paramCount] do
    let n := entryParamName actionIndex i
    emittedParams := emittedParams.push n
    nondets := nondets.push { name := n, domain := u64Domain }
  let ctx : LowerCtx := { slots, params := emittedParams, declaredErrors }
  let flat ← compileMutateOps ctx selfResult {} none method.ops.toList
  unless flat.stores.size ≤ maxStores do
    emitError s!"entry '{method.name}' store count exceeds limit"
  unless flat.checks.size ≤ maxChecks do
    emitError s!"entry '{method.name}' check count exceeds limit"
  for (_, cond) in flat.checks do validateExpr cond
  for (_, post) in flat.stores do validateExpr post
  let (pures0, okName, failName) := checkCascade flat.checks
  let mut pures := pures0
  match flat.result? with
  | some r =>
      validateExpr r
      pures := pures.push { name := "resR", value := r }
  | none => pure ()
  let mut assigns : Array QAssign := #[
    { target := "pf_last_action", value := .intLit (toString actionIndex) },
    { target := "pf_last_ok", value := .name okName },
    { target := "pf_last_failure", value := .name failName } ]
  -- This entry's last args/result update; every other entry's stutter.
  for entry in entries do
    if entry.name == method.name then
      for i in [0:entry.paramCount] do
        assigns := assigns.push {
          target := lastArgName entry.name i
          value := .name (entryParamName actionIndex i) }
      match flat.result? with
      | some _ =>
          assigns := assigns.push {
            target := selfResult
            value := .ifThenElse (.name okName) (.name "resR") (.name selfResult) }
      | none =>
          assigns := assigns.push { target := selfResult, value := .name selfResult }
    else
      for i in [0:entry.paramCount] do
        assigns := assigns.push {
          target := lastArgName entry.name i
          value := .name (lastArgName entry.name i) }
      let otherResult := lastResultName entry.name
      assigns := assigns.push { target := otherResult, value := .name otherResult }
  -- Business state: success applies the post value, failure stutters.
  let mut written : Array String := #[]
  for (leaf, post) in flat.stores do
    written := written.push leaf
    let sn := stateName leaf
    assigns := assigns.push {
      target := sn, value := .ifThenElse (.name okName) post (.name sn) }
  for leaf in slots do
    unless written.contains leaf do
      let sn := stateName leaf
      assigns := assigns.push { target := sn, value := .name sn }
  pure { nondets, pures, assigns }

private def emitInitBranch (slots : Array String) (entries : Array EntryInfo)
    (init? : Option (Core.IR.Method Ops.ValKind Ops.OpExt)) :
    Except String QActionBranch := do
  let mut nondets : Array QNondetBind := #[]
  let mut values : Array QExpr := #[]
  match init? with
  | some m =>
      unless m.paramCount ≤ maxParams do
        emitError "init parameter count exceeds limit"
      let mut params : Array String := #[]
      for i in [0:m.paramCount] do
        let n := initParamName i
        params := params.push n
        nondets := nondets.push { name := n, domain := u64Domain }
      values ← compileInitOps { slots, params } #[] m.ops.toList
      for v in values do validateExpr v
  | none =>
      -- Synthetic empty init: zeroed state and instrumentation.
      values := slots.map fun _ => .intLit "0"
  let mut assigns : Array QAssign := #[
    { target := "pf_last_action", value := .intLit "0" },
    { target := "pf_last_ok", value := .boolLit true },
    { target := "pf_last_failure", value := .intLit "0" } ]
  for (leaf, v) in slots.zip values do
    assigns := assigns.push { target := stateName leaf, value := v }
  for entry in entries do
    for i in [0:entry.paramCount] do
      assigns := assigns.push { target := lastArgName entry.name i, value := .intLit "0" }
    assigns := assigns.push { target := lastResultName entry.name, value := .intLit "0" }
  pure { nondets, pures := #[], assigns }

-- ---------------------------------------------------------------------------
-- Module assembly
-- ---------------------------------------------------------------------------

private def assemble (program : Core.IR.Program Ops.ValKind Ops.OpExt) :
    Except String QModule := do
  unless isIdent program.name do
    emitError s!"program name '{program.name}' is not a safe Quint identifier"
  unless program.slots.size ≤ maxSlots do
    emitError "program exceeds the state slot limit"
  unless program.methods.size ≤ maxMethods do
    emitError "program exceeds the method limit"
  let slots := program.slots.map (·.name)
  for slot in program.slots do
    unless isIdent slot.name do
      emitError s!"state leaf '{slot.name}' is not a safe identifier"
    unless slot.width == 8 do
      emitError s!"state leaf '{slot.name}' is not a UInt64 leaf (width {slot.width})"
  unless slots.toList.eraseDups.length == slots.size do
    emitError "duplicate state leaf names"
  let mut seenMethods : Array String := #[]
  for m in program.methods do
    unless isIdent m.name do
      emitError s!"method name '{m.name}' is not a safe identifier"
    if seenMethods.contains m.name then
      emitError s!"duplicate method name '{m.name}'"
    seenMethods := seenMethods.push m.name
  let inits := program.methods.filter (·.kind == .init)
  unless inits.size ≤ 1 do
    emitError "at most one init method"
  let entryMethods := program.methods.filter (·.kind == .increment)
  let viewMethods := program.methods.filter (·.kind == .get)
  let declaredErrors :=
    program.methods.foldl (init := #[]) fun acc m => collectNamedErrors m.ops acc
  let entries : Array EntryInfo :=
    entryMethods.map fun m => { name := m.name, paramCount := m.paramCount }
  let mut decls : Array QDecl :=
    #[.pureConst "PF_MAX_U64" "int" (.intLit maxU64Lit)]
  -- Business state.
  for leaf in slots do
    decls := decls.push (.varDecl (stateName leaf) "int")
  -- Instrumentation.
  decls := decls.push (.varDecl "pf_last_action" "int")
  decls := decls.push (.varDecl "pf_last_ok" "bool")
  decls := decls.push (.varDecl "pf_last_failure" "int")
  for entry in entries do
    for i in [0:entry.paramCount] do
      decls := decls.push (.varDecl (lastArgName entry.name i) "int")
    decls := decls.push (.varDecl (lastResultName entry.name) "int")
  -- Views as pure defs under a target-owned namespace.
  for vidx in [0:viewMethods.size] do
    let m := viewMethods[vidx]!
    unless m.paramCount ≤ maxParams do
      emitError s!"view '{m.name}' parameter count exceeds limit"
    let mut params : Array String := #[]
    for i in [0:m.paramCount] do
      params := params.push (viewParamName vidx i)
    let body ← compileViewOps { slots, params, declaredErrors } m.ops.toList
    validateExpr body
    decls := decls.push
      (.pureDef (viewName m.name) (params.map fun n => (n, "int")) "int" body)
  -- init action (synthetic all-zero when the program has no init method).
  let initBranch ← emitInitBranch slots entries inits[0]?
  decls := decls.push (.actionInit initBranch)
  -- step action: one branch per entry; view-only programs stutter.
  let mut branches : Array QActionBranch := #[]
  for aidx in [0:entryMethods.size] do
    let branch ←
      emitEntryBranch slots entries declaredErrors entryMethods[aidx]! (aidx + 1)
    branches := branches.push branch
  if branches.isEmpty then
    let mut assigns : Array QAssign := #[
      { target := "pf_last_action", value := .intLit "0" },
      { target := "pf_last_ok", value := .boolLit true },
      { target := "pf_last_failure", value := .intLit "0" } ]
    for leaf in slots do
      let sn := stateName leaf
      assigns := assigns.push { target := sn, value := .name sn }
    branches := branches.push { assigns }
  decls := decls.push (.actionStep branches)
  pure {
    name := moduleNameOf program.name
    headerComment :=
      "// Generated by ProofForgeCommon (Quint default target).\n" ++
      "// Source-only Quint model; no Quint CLI, Apalache, TLC, or JVM is invoked."
    decls
  }

-- ---------------------------------------------------------------------------
-- Renderer
-- ---------------------------------------------------------------------------

private def binOpSym : QBinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .and => "and" | .or => "or"

private def binOpPrecedence : QBinOp → Nat
  | .or => 10
  | .and => 20
  | .eq | .ne => 30
  | .lt | .le | .gt | .ge => 40
  | .add | .sub => 50
  | .mul | .div | .mod => 60

private def wrapExpr (requested own : Nat) (rendered : String) : String :=
  if own < requested then "(" ++ rendered ++ ")" else rendered

/-- Precedence-aware Quint renderer. Root `if` and `not` expressions must not
    acquire redundant parentheses. -/
private partial def renderExprPrec (requested : Nat) : QExpr → String
  | .name id => id
  | .intLit v => v
  | .boolLit true => "true"
  | .boolLit false => "false"
  | .binary op l r =>
      let own := binOpPrecedence op
      wrapExpr requested own
        s!"{renderExprPrec own l} {binOpSym op} {renderExprPrec (own + 1) r}"
  | .not o => wrapExpr requested 80 s!"not({renderExprPrec 0 o})"
  | .call "to" args =>
      -- special-case `0.to(PF_MAX_U64)` method form
      match args[0]?, args[1]? with
      | some a, some b =>
          wrapExpr requested 80 s!"{renderExprPrec 81 a}.to({renderExprPrec 0 b})"
      | _, _ =>
          let argStr := String.intercalate ", " (args.map (renderExprPrec 0)).toList
          wrapExpr requested 80 s!"to({argStr})"
  | .call callee args =>
      let argStr := String.intercalate ", " (args.map (renderExprPrec 0)).toList
      wrapExpr requested 80 s!"{callee}({argStr})"
  | .ifThenElse c t e =>
      wrapExpr requested 5
        s!"if ({renderExprPrec 0 c}) {renderExprPrec 0 t} else {renderExprPrec 0 e}"

private def renderExpr (expr : QExpr) : String :=
  renderExprPrec 0 expr

private def indent (n : Nat) (s : String) : String :=
  String.ofList (List.replicate n ' ') ++ s

private def renderBranch (level : Nat) (br : QActionBranch) : Array String := Id.run do
  let mut lines : Array String := #[]
  lines := lines.push (indent level "{")
  for nd in br.nondets do
    lines := lines.push (indent (level + 2) s!"nondet {nd.name} = {renderExpr nd.domain}")
  for p in br.pures do
    lines := lines.push (indent (level + 2) s!"val {p.name} = {renderExpr p.value}")
  lines := lines.push (indent (level + 2) "all {")
  for a in br.assigns do
    lines := lines.push (indent (level + 4) s!"{a.target}' = {renderExpr a.value},")
  lines := lines.push (indent (level + 2) "}")
  lines := lines.push (indent level "}")
  pure lines

private def renderDecl (d : QDecl) : Array String :=
  match d with
  | .pureConst name ty value =>
      #[s!"  pure def {name}: {ty} = {renderExpr value}"]
  | .varDecl name ty =>
      #[s!"  var {name}: {ty}"]
  | .pureDef name params retTy body =>
      if params.isEmpty then
        #[s!"  pure def {name}: {retTy} = {renderExpr body}"]
      else
        let ps := String.intercalate ", "
          (params.map fun (n, t) => s!"{n}: {t}").toList
        #[s!"  pure def {name}({ps}): {retTy} = {renderExpr body}"]
  | .actionInit br => Id.run do
      let mut lines : Array String := #["  action init = {"]
      for nd in br.nondets do
        lines := lines.push (indent 4 s!"nondet {nd.name} = {renderExpr nd.domain}")
      for p in br.pures do
        lines := lines.push (indent 4 s!"val {p.name} = {renderExpr p.value}")
      lines := lines.push (indent 4 "all {")
      for a in br.assigns do
        lines := lines.push (indent 6 s!"{a.target}' = {renderExpr a.value},")
      lines := lines.push (indent 4 "}")
      lines := lines.push "  }"
      pure lines
  | .actionStep branches => Id.run do
      let mut lines : Array String := #["  action step = any {"]
      for i in [0:branches.size] do
        match branches[i]? with
        | some br =>
            lines := lines ++ renderBranch 4 br
            if i + 1 < branches.size then
              lines := lines.push (indent 4 ",")
        | none => pure ()
      lines := lines.push "  }"
      pure lines

private def renderModule (m : QModule) : String := Id.run do
  let mut lines : Array String := #[]
  lines := lines.push m.headerComment
  lines := lines.push s!"module {m.name} \{"
  for d in m.decls do
    lines := lines.push ""
    lines := lines ++ renderDecl d
  lines := lines.push "}"
  lines := lines.push ""
  pure (String.intercalate "\n" lines.toList)

-- ---------------------------------------------------------------------------
-- Public entry points
-- ---------------------------------------------------------------------------

/-- Lower a program to `.qnt` source text (no shared boundary validation). -/
def emitProgram (program : Core.IR.Program Ops.ValKind Ops.OpExt) :
    Except String String := do
  let m ← assemble program
  pure (renderModule m)

/-- Full default pipeline: shared boundary validation (boundary schemas, op
    well-formedness, CFG lower/optimize) followed by Quint emission. -/
def compileProgram (program : Core.IR.Program Ops.ValKind Ops.OpExt) :
    Except String String := do
  let projected ← Core.Target.projectProgram registration program
  emitProgram projected

end ProofForge.Quint.Emit
