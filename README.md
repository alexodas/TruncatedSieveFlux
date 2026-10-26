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

## Why this formalization may be interesting

The contribution is **not a new number-theoretic cancellation theorem**.
Its potential value is to make the effect of truncating a classical Möbius
divisor sum mathematically explicit and machine-checkable. For every lower
threshold `A : ℝ`, every indexed upper cutoff `K : ℕ → ℝ`, every index
`k : ℕ`, and `x ≥ 2`, the proved results give

```text
density K A k x moebiusReal
  = |1 - omittedMass K A k x moebiusReal|
  ≤ 1 + omittedCount K A k x
```

Here `density` is the absolute value of a **finite signed divisor sum**,
not an asymptotic density of primes. The underlying finite sums range over
`Nat.divisors n` for `n < Nat.ceil x`; `omittedCount` counts omitted
**divisor incidences** across those values of `n`, not just distinct divisors.

Three aspects may make the development useful:

1. **An exact truncation-error identity.** Classical Möbius divisor
   cancellation says that the full finite sum is 1 (for `x ≥ 2`).
   Partitioning each divisor set into admitted and omitted terms identifies
   the entire difference from that full sum as the signed omitted mass.
   This requires no monotonicity or growth assumption on `K`.
2. **A clear boundary between bookkeeping and analytic estimates.** The
   inequality using `omittedCount` is unconditional but generally coarse.
   A genuinely sharper sieve estimate would require further hypotheses or
   cancellation information about `omittedMass`; none is established here.
   The separate `sieveIndex` definition supplies a possible index choice,
   but the proved theorems do not assert an asymptotic bound for that choice.
3. **A small reusable formal-verification case study.** The proof tests
   finite-set partitioning, the classical Möbius identity, coercions to the
   reals, and absolute-value bounds. Independent `Challenge.lean` and
   `Solution.lean` modules, plus Comparator checks using Lean, NanoDa,
   and con-ron, make the result reproducible and potentially useful as an
   example for extending or auditing formal arithmetic arguments.

These are reasons to consider the **formalization** useful, not claims of
mathematical originality, a nontrivial asymptotic estimate, or acceptance
by Palomar.

## Authorship and AI assistance

**Author and responsible maintainer:** Alessandro Odasso.

**AI-use disclosure:** ChatGPT **GPT-6 with High thinking effort** (as reported
by the contributor) was used to assist with Lean proof drafting, debugging,
repository setup, and GitHub Actions troubleshooting. This was an AI-assisted,
human-directed formalization. The proofs passed Lean, NanoDa, and con-ron in
GitHub Actions; independent mathematical peer review has not been performed.
The structured disclosure is also recorded in `formalization.yaml`.

## Project files

- `Challenge.lean`: standalone mathematical interface (definitions, declarations
  to audit, and deliberate theorem holes).
- `Solution.lean`: duplicates the independent definitions and supplies proofs.
- `comparator.json`: compares the two named theorem statements and proofs.
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
