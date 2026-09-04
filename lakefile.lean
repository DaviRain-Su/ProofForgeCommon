import Lake
open Lake DSL

package «proofforge-common» where
  version := v!"0.2.0"

/-- Shared ProofForge surface: Attr, Core (IR/Ops/CFG/Target/…), Crypto, Profile,
    and the Quint default target (dialect, default registration, `.qnt` emitter).
    Single source for the EVM / SVM / NEAR / Psy target repositories. Depends on
    Lean + Std only — no Mathlib, no target SDKs, no extractors. -/
@[default_target]
lean_lib ProofForgeCore where
  roots := #[
    `ProofForge.Attr,
    `ProofForge.Core.Codec,
    `ProofForge.Core.Collections,
    `ProofForge.Core.CFG,
    `ProofForge.Core.Eval,
    `ProofForge.Core.Except,
    `ProofForge.Core.FixedPoint,
    `ProofForge.Quint.Ops,
    `ProofForge.Quint.Registration,
    `ProofForge.Quint.Emit,
    `ProofForge.Core.IR,
    `ProofForge.Core.Math,
    `ProofForge.Core.Ops,
    `ProofForge.Core.SafeCast,
    `ProofForge.Core.Schema,
    `ProofForge.Core.Target,
    `ProofForge.Core.Value,
    `ProofForge.Crypto.Keccak,
    `ProofForge.Crypto.Sha256,
    `ProofForge.Crypto.Sha256Compat,
    `ProofForge.Profile,
    `ProofForge.RuntimeImports
  ]

/-- Pure-Core specs. Namespace deliberately outside `ProofForge.*` and `Tests.*`:
    a dep glob over either would claim that namespace away from consumer repos. -/
lean_lib ProofForgeCoreTests where
  globs := #[.submodules `ProofForgeCoreTests]

/-- Writes the shared Quint fixtures as `.qnt` modules; the CI Quint CLI gate
    parses and typechecks them with the real Quint toolchain. Root namespace
    stays outside `ProofForge.*` for the same reason as the specs. -/
lean_exe quintEmit where
  root := `ProofForgeQuintTool.Main
