# ProofForgeCommon

Shared ProofForge surface for the target compiler repositories
([ProofForgeEvm](https://github.com/DaviRain-Su/ProofForgeEvm),
[ProofForgeSvm](https://github.com/DaviRain-Su/ProofForgeSvm),
[ProofForgeNear](https://github.com/DaviRain-Su/ProofForgeNear),
[ProofForgePsy](https://github.com/DaviRain-Su/ProofForgePsy)).

Single source of truth for:

- `ProofForge.Attr` — `pf_entry` / `pf_inline` / `pf_boundary` tag attributes
- `ProofForge.Core.*` — target-neutral IR, Ops, CFG, projection (`Core.Target`), codec,
  schema, value, math, fixed-point, collections, safe-cast, eval, except
- `ProofForge.Crypto.*` — Sha256 / Keccak (host + source-level semantics)
- `ProofForge.Profile` — compile-root profile checks

Depends on Lean + Std only. No Mathlib, no target SDKs, no extractors.
Module paths mirror the consumer repositories (`ProofForge/Core/Codec.lean` …), so
`import ProofForge.Core.*` keeps working unchanged after a target repo switches to
`require «proofforge-common»`.

## Layout

```
ProofForge/        shared library (lean_lib ProofForgeCore)
Tests/             pure-Core specs (CoreCodecSpec, CoreCollectionsSpec, CoreMathSpec)
```

Target-specific layers (target Runtimes, SDKs, extractors, CLI, and extended
attributes such as `pf_svm_raw*`) stay in the target repositories.

## Consuming

```lean
-- path require while iterating locally:
require «proofforge-common» from "../ProofForgeCommon"
-- or pinned git require for CI / release:
require «proofforge-common» from git
  "https://github.com/DaviRain-Su/ProofForgeCommon.git" @ "<tag-or-sha>"
```

`lean-toolchain` here is pinned to the same version as the consumer repositories;
bump all five together.

## Development

```sh
lake build            # builds ProofForgeCore + Tests
lake build Tests.CoreCodecSpec Tests.CoreCollectionsSpec Tests.CoreMathSpec
```