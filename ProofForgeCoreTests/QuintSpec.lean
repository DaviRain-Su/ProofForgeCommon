import ProofForge.Quint.Emit

/-!
Specs for the Quint default target: dialect, registration, and the `.qnt`
emitter (`ProofForge.Quint.Emit`). Fixtures are hand-built extension-free Core
programs; golden substrings pin the emitted Quint surface.
-/

namespace ProofForgeCoreTests.QuintSpec
open ProofForge
open ProofForge.Core

private abbrev V := Core.Ops.Val Quint.Ops.ValKind
private abbrev O := Core.Ops.Op Quint.Ops.ValKind Quint.Ops.OpExt

private def stateRead : V := .field (.arg 0) "value"

/-- Canonical counter: guard-folded increment, per-leaf `returnState` init,
    expression view. -/
private def counter : IR.Program Quint.Ops.ValKind Quint.Ops.OpExt :=
  { name := "Counter"
    slots := #[{ name := "value" }]
    methods := #[
      { kind := .init, name := "init", ixName := "initialize", paramCount := 1,
        ops := #[.returnState (.arg 0)] },
      { kind := .increment, name := "increment", ixName := "increment",
        paramCount := 1,
        ops := #[
          .checkedAddU64 stateRead (.arg 0),
          .okState (.lit 0),
          .errorOverflow ] },
      { kind := .get, name := "get", ixName := "get", paramCount := 0,
        ops := #[.returnU64 stateRead] } ] }

private def counterText : String :=
  match Quint.Emit.compileProgram counter with
  | .ok text => text
  | .error reason => panic! s!"counter must compile: {reason}"

#guard counterText.contains "module PFModel_Counter {"
#guard counterText.contains "pure def PF_MAX_U64: int = 18446744073709551615"
#guard counterText.contains "var pf_state_value: int"
#guard counterText.contains "var pf_last_action: int"
#guard counterText.contains "var pf_last_ok: bool"
#guard counterText.contains "var pf_last_failure: int"
#guard counterText.contains "var pf_last_increment_arg0: int"
#guard counterText.contains "var pf_last_increment_result: int"
#guard counterText.contains "pure def pf_view_get: int = pf_state_value"
#guard counterText.contains "nondet pf_init_arg0 = oneOf(0.to(PF_MAX_U64))"
#guard counterText.contains "nondet pf_arg_a1_0 = oneOf(0.to(PF_MAX_U64))"
-- Checked add: exact overflow condition on unbounded ints, implicit writeback.
#guard counterText.contains "val ck0 = pf_state_value + pf_arg_a1_0 <= PF_MAX_U64"
#guard counterText.contains "val resR = pf_state_value + pf_arg_a1_0"
#guard counterText.contains "val fail1 = if (not(ck0)) 1 else 0"
-- Failure stutters business state and the result var.
#guard
  counterText.contains
    "pf_state_value' = if (ok1) pf_state_value + pf_arg_a1_0 else pf_state_value"
#guard
  counterText.contains
    "pf_last_increment_result' = if (ok1) resR else pf_last_increment_result"
#guard counterText.contains "pf_last_action' = 1"
#guard counterText.contains "pf_state_value' = pf_init_arg0"

/-- Guarded mutate: `ite` with an explicit-store arm and a declared-revert arm
    flattens to conditional assignments with a 256+ revert code. -/
private def guarded : IR.Program Quint.Ops.ValKind Quint.Ops.OpExt :=
  { name := "Guarded"
    slots := #[{ name := "value" }]
    methods := #[
      { kind := .init, name := "init", ixName := "initialize", paramCount := 0,
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "deposit", ixName := "deposit",
        paramCount := 1,
        ops := #[
          .ite .lt (.arg 0) (.lit 100)
            #[.storeField "value" (.addU64 stateRead (.arg 0)), .okState (.lit 1)]
            #[.errorNamed "TooLarge"] ] } ] }

private def guardedText : String :=
  match Quint.Emit.compileProgram guarded with
  | .ok text => text
  | .error reason => panic! s!"guarded must compile: {reason}"

#guard guardedText.contains "var pf_last_deposit_result: int"
#guard guardedText.contains "val ck0 = if (pf_arg_a1_0 < 100) true else false"
#guard guardedText.contains "val fail1 = if (not(ck0)) 256 else 0"
#guard guardedText.contains
  ("pf_state_value' = if (ok1) if (pf_arg_a1_0 < 100) " ++
    "pf_state_value + pf_arg_a1_0 else pf_state_value else pf_state_value")
#guard
  guardedText.contains
    "val resR = if (pf_arg_a1_0 < 100) 1 else pf_last_deposit_result"

/-- Two slots, explicit store to one leaf: the other stutters. Two entries
    render as two `any` branches. -/
private def twoSlots : IR.Program Quint.Ops.ValKind Quint.Ops.OpExt :=
  { name := "TwoSlots"
    slots := #[{ name := "a" }, { name := "b" }]
    methods := #[
      { kind := .increment, name := "setA", ixName := "setA", paramCount := 1,
        ops := #[.storeField "a" (.arg 0), .okState (.lit 0)] },
      { kind := .increment, name := "setB", ixName := "setB", paramCount := 1,
        ops := #[.storeField "b" (.arg 0), .okState (.lit 0)] } ] }

private def twoSlotsText : String :=
  match Quint.Emit.compileProgram twoSlots with
  | .ok text => text
  | .error reason => panic! s!"twoSlots must compile: {reason}"

-- No init method: synthetic all-zero init.
#guard twoSlotsText.contains "pf_state_a' = 0"
#guard twoSlotsText.contains "pf_state_b' = 0"
#guard twoSlotsText.contains "pf_state_a' = if (ok0) pf_arg_a1_0 else pf_state_a"
#guard twoSlotsText.contains "pf_state_b' = pf_state_b"
#guard twoSlotsText.contains "pf_state_b' = if (ok0) pf_arg_a2_0 else pf_state_b"
-- Per-entry instrumentation: the other entry's vars stutter in each branch.
#guard twoSlotsText.contains "pf_last_setA_result' = pf_last_setA_result"
#guard twoSlotsText.contains "pf_last_setB_result' = pf_last_setB_result"

/-- Branching view: both arms return, lowered to one if-then-else. -/
private def branchingView : IR.Program Quint.Ops.ValKind Quint.Ops.OpExt :=
  { name := "Bounded"
    slots := #[{ name := "value" }]
    methods := #[
      { kind := .get, name := "isLarge", ixName := "isLarge", paramCount := 0,
        ops := #[
          .ite .ge stateRead (.lit 10)
            #[.returnU64 (.lit 1)]
            #[.returnU64 (.lit 0)] ] } ] }

#guard
  match Quint.Emit.compileProgram branchingView with
  | .ok text => text.contains "pure def pf_view_isLarge: int = if (pf_state_value >= 10) 1 else 0"
  | .error _ => false

-- ---------------------------------------------------------------------------
-- Fail-closed boundary
-- ---------------------------------------------------------------------------

private def expectEmitError (program : IR.Program Quint.Ops.ValKind Quint.Ops.OpExt)
    (needle : String) : Bool :=
  match Quint.Emit.emitProgram program with
  | .error reason => reason.contains needle
  | .ok _ => false

private def mutateWith (ops : Array O) : IR.Program Quint.Ops.ValKind Quint.Ops.OpExt :=
  { name := "Bad"
    slots := #[{ name := "value" }]
    methods := #[
      { kind := .increment, name := "go", ixName := "go", paramCount := 1, ops } ] }

-- Bitwise values are outside the default subset.
#guard expectEmitError (mutateWith #[.okState (.bitAnd stateRead (.arg 0))]) "bitwise"
-- Unknown store leaf fails closed.
#guard expectEmitError (mutateWith #[.storeField "nope" (.lit 1), .okState (.lit 0)])
  "unknown state leaf"
-- Typed errors are outside the default subset.
#guard expectEmitError
  (mutateWith #[.errorTyped { constructor := "E", args := #[] }]) "typed errors"
-- Vector reads are outside the default subset.
#guard expectEmitError (mutateWith #[.okState (.indexGet (.arg 0) "v" (.lit 0) 4)])
  "vector index reads"
-- Loops are outside the default subset.
#guard expectEmitError (mutateWith #[.forBody 3 #[.okState (.lit 0)]]) "loops"
-- Events are outside the default subset.
#guard expectEmitError (mutateWith #[.emitEvent "Ev" (.lit 0)]) "events"
-- External calls are outside the default subset.
#guard expectEmitError (mutateWith #[.externalCall #["callee"] #[]]) "external calls"
-- A mutating body must end in a terminal.
#guard expectEmitError (mutateWith #[.storeField "value" (.arg 0)]) "must end in okState"
-- Init admits no fallible operations.
#guard
  expectEmitError
    { name := "BadInit"
      slots := #[{ name := "value" }]
      methods := #[
        { kind := .init, name := "init", ixName := "initialize", paramCount := 1,
          ops := #[.checkedAddU64 stateRead (.arg 0), .returnState (.arg 0)] } ] }
    "init admits only"
-- Init must return exactly one value per slot.
#guard
  expectEmitError
    { name := "ShortInit"
      slots := #[{ name := "a" }, { name := "b" }]
      methods := #[
        { kind := .init, name := "init", ixName := "initialize", paramCount := 0,
          ops := #[.returnState (.lit 0)] } ] }
    "exactly 2 state values"
-- Views must be side-effect free.
#guard
  expectEmitError
    { name := "BadView"
      slots := #[{ name := "value" }]
      methods := #[
        { kind := .get, name := "get", ixName := "get", paramCount := 0,
          ops := #[.storeField "value" (.lit 1), .returnU64 (.lit 0)] } ] }
    "side-effect free"

-- ---------------------------------------------------------------------------
-- Registration / projection integration
-- ---------------------------------------------------------------------------

-- Projection (shared boundary validation) accepts the counter and does not
-- change the emitted text.
#guard
  match Core.Target.projectProgram Quint.registration counter with
  | .ok projected =>
      match Quint.Emit.emitProgram projected, Quint.Emit.emitProgram counter with
      | .ok a, .ok b => a == b
      | _, _ => false
  | .error _ => false

-- Projection rejects a program whose CFG is malformed (ops after a terminal).
#guard
  match Core.Target.projectProgram Quint.registration
      (mutateWith #[.okState (.lit 0), .storeField "value" (.lit 1)]) with
  | .error reason => reason.contains "terminal"
  | .ok _ => false

end ProofForgeCoreTests.QuintSpec
