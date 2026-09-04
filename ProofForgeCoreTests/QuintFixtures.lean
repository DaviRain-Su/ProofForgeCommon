import ProofForge.Quint.Emit

/-!
Shared Quint fixture programs: consumed by `ProofForgeCoreTests.QuintSpec`
(`#guard` golden checks) and by the `quintEmit` executable, which writes them
as `.qnt` files for the CI Quint CLI parse/typecheck gate.
-/

namespace ProofForgeCoreTests.QuintFixtures

open ProofForge
open ProofForge.Core

abbrev V := Core.Ops.Val Quint.Ops.ValKind
abbrev O := Core.Ops.Op Quint.Ops.ValKind Quint.Ops.OpExt

def stateRead : V := .field (.arg 0) "value"

/-- Canonical counter: guard-folded increment, per-leaf `returnState` init,
    expression view. -/
def counter : IR.Program Quint.Ops.ValKind Quint.Ops.OpExt :=
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

/-- Guarded mutate: `ite` with an explicit-store arm and a declared-revert arm
    flattens to conditional assignments with a 256+ revert code. -/
def guarded : IR.Program Quint.Ops.ValKind Quint.Ops.OpExt :=
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

/-- Two slots, explicit store to one leaf: the other stutters. No init method:
    the emitter synthesizes an all-zero init. -/
def twoSlots : IR.Program Quint.Ops.ValKind Quint.Ops.OpExt :=
  { name := "TwoSlots"
    slots := #[{ name := "a" }, { name := "b" }]
    methods := #[
      { kind := .increment, name := "setA", ixName := "setA", paramCount := 1,
        ops := #[.storeField "a" (.arg 0), .okState (.lit 0)] },
      { kind := .increment, name := "setB", ixName := "setB", paramCount := 1,
        ops := #[.storeField "b" (.arg 0), .okState (.lit 0)] } ] }

/-- Branching view: both arms return, lowered to one if-then-else. -/
def branchingView : IR.Program Quint.Ops.ValKind Quint.Ops.OpExt :=
  { name := "Bounded"
    slots := #[{ name := "value" }]
    methods := #[
      { kind := .get, name := "isLarge", ixName := "isLarge", paramCount := 0,
        ops := #[
          .ite .ge stateRead (.lit 10)
            #[.returnU64 (.lit 1)]
            #[.returnU64 (.lit 0)] ] } ] }

/-- Every fixture the `quintEmit` executable writes. -/
def all : Array (IR.Program Quint.Ops.ValKind Quint.Ops.OpExt) :=
  #[counter, guarded, twoSlots, branchingView]

end ProofForgeCoreTests.QuintFixtures
