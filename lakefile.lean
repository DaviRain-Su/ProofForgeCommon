import Lake
open Lake DSL

package «proofforge-common» where
  version := v!"0.1.0"

/-- Shared ProofForge surface: Attr, Core (IR/Ops/CFG/Target/…), Crypto, Profile.
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
    `ProofForge.Profile
  ]

/-- Pure-Core specs. Namespace deliberately outside `ProofForge.*` and `Tests.*`:
    a dep glob over either would claim that namespace away from consumer repos. -/
lean_lib ProofForgeCoreTests where
  globs := #[.submodules `ProofForgeCoreTests]
