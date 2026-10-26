# Truncated Möbius divisor sieve — Lean 4

A self-contained Lean 4/Mathlib project for two **elementary finite** results:

1. An exact residual identity for the admitted Möbius mass of an indexed,
   truncated divisor sieve.
2. An unconditional upper bound by one plus the number of omitted divisor
   incidences.

The mathematical statement is **not** an asymptotic cancellation estimate.
There are no claims about the general growth of arbitrary sieve thresholds.
The `Challenge.lean` file deliberately has the two `sorry` markers that a
Comparator challenge is expected to contain. `Solution.lean` contains no
`sorry` and imports only Mathlib. **Both Lean modules compile successfully**
under GitHub Actions (Lean v4.35.0-rc2; run 40246677026).
Comparator accepted both theorem declarations using Lean, NanoDa and con-ron
(GitHub Actions run 40247244629). An independent mathematical review has
**not yet** been completed.

## Project files

- `Challenge.lean`: standalone mathematical interface (definitions, declarations
  to audit, and deliberate theorem holes).
- `Solution.lean`: duplicates the independent definitions and supplies proofs.
- `comparator.json`: checks the two named theorems and all eight definitions.
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`: pinned Lake project,
  copied consistently from the public Palomar starter dependencies.
- `formalization.yaml`: project scope, attribution, AI use, and review status.
- `LICENSE`: Apache 2.0.

## Build and check

Requires `elan` (Lean version manager), Git, internet access for dependencies,
and sufficient disk space for Mathlib. In the project root:

```sh
lake exe cache get
lake build
./scripts/check.sh
```

The last command checks the proof with `lake build Challenge Solution` and
`lake comparator --config`, registering the bundled independent kernels in a
temporary Comparator configuration, as in the Palomar starter project.
The check requires `bwrap` in addition to Lean and the checked-in dependencies.

## Before public submission

1. Replace the generic author and maintainer identifiers in `formalization.yaml`
   with correct, authorized contributor names.
2. Re-run `./scripts/check.sh` to reproduce the passing Comparator check and archive its results.
3. Review the theorem statements and provenance independently of the model.
4. Commit the final `lake-manifest.json` if Lake regenerates it; keep every
   dependency pinned.
5. Push a **public** GitHub repository, then submit its full 40-character
   commit SHA to Palomar. Repository files alone are not a submitted snapshot.

The repository is a draft. Its mathematical contribution is primarily the
formal bookkeeping of truncation; no originality or registry acceptance is
implied.