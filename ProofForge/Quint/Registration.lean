import ProofForge.Core.Target
import ProofForge.Quint.Ops

/-!
# ProofForge.Quint.Registration — default target registration

Source and target dialects coincide (both are the extension-free Quint
dialect), so the extension projections are identity functions discharged by
`nomatch`. The registration exists to run the shared boundary validation —
boundary schemas, op well-formedness, CFG lower/optimize — over hand-built
Core programs before Quint emission.
-/

namespace ProofForge.Quint

/-- Static registration of the default Quint projection. -/
def registration :
    Core.Target.Registration Ops.ValKind Ops.OpExt Ops.ValKind Ops.OpExt where
  name := "Quint"
  projectValExt := fun kind =>
    kind.elim (motive := fun _ => Except String Ops.ValKind)
  projectOpExt := fun _ payload =>
    payload.elim (motive := fun _ =>
      Except String (Ops.OpExt (Core.Ops.Val Ops.ValKind)))
  valArity := Ops.ValKind.arity
  opWellFormed := Ops.Op.wellFormed
  cfgDialect := {
    mapValues := fun _ payload =>
      payload.elim (motive := fun _ => Ops.OpExt (Core.Ops.Val Ops.ValKind))
    values := fun payload =>
      payload.elim (motive := fun _ => Array (Core.Ops.Val Ops.ValKind))
    payloadEq := fun left _ =>
      left.elim (motive := fun _ => Bool)
  }

end ProofForge.Quint
