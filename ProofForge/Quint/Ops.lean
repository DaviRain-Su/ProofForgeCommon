import ProofForge.Core.Ops

/-!
# ProofForge.Quint.Ops — Quint default-target dialect

The Quint default target consumes only the target-neutral Core language:
UInt64 state leaves, `letLocal`, checked arithmetic statements, `storeField`,
`okState`, error terminals, `ite`, and `returnU64` / `returnState`. It owns no
target-specific value or effect intrinsics, so both extension types are
intentionally empty; any future extension becomes an explicit, reviewable
constructor.
-/

namespace ProofForge.Quint.Ops

/-- Quint value extensions: none. Recursive operands would live in
    `Core.Ops.Val.ext`; the default target admits none. -/
inductive ValKind where
  deriving BEq, Repr, DecidableEq

/-- No payloads exist; elimination is by `nomatch`. -/
def ValKind.elim {motive : ValKind → Sort _} (x : ValKind) : motive x :=
  nomatch x

def ValKind.arity : ValKind → Nat :=
  fun kind => nomatch kind

abbrev Val := ProofForge.Core.Ops.Val ValKind
abbrev Cmp := ProofForge.Core.Ops.Cmp

/-- Quint effect extensions: none. The default subset never produces
    `Op.ext`. -/
inductive OpExt (V : Type) where
  deriving BEq, Repr

/-- No payloads exist; elimination is by `nomatch`. -/
def OpExt.elim {V : Type} {motive : OpExt V → Sort _} (x : OpExt V) : motive x :=
  nomatch x

def OpExt.wellFormed (x : OpExt Val) : Bool :=
  nomatch x

def Op.wellFormed (op : ProofForge.Core.Ops.Op ValKind OpExt) : Bool :=
  ProofForge.Core.Ops.Op.wellFormed ValKind.arity
    (fun kind n => n == ValKind.arity kind) OpExt.wellFormed op

end ProofForge.Quint.Ops
