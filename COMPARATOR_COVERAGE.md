# Comparator coverage and validation boundaries

This file records which declarations are **independent statement comparisons**
and which are only checked through Lean module/kernel replay.
It is not a claim of complete named-theorem Comparator coverage.

## Mechanical checks

1. The standard CI build elaborates `Challenge`, `Solution`,
   `FourthMomentResearch`, `CovarianceChallenge` and
   `CovarianceSolution`.
2. CI separately runs `leanchecker` for each **completed** proof module
   (`Solution`, `FourthMomentResearch` and `CovarianceSolution`).
   This kernel replay checks all local theorem declarations, but is
   *another check with Lean's kernel*, not an independent implementation.
3. The existing `comparator.json` performs a statement/proof comparison
   and independent-kernel replay of
   `TruncatedSieveFlux.moebius_log_cutoff_residual_approximation`.
4. The `comparator-covariance.json` performs independent statement/proof
   comparisons of the following **five** theorem statements.
   All five passed NanoDa and con-ron in GitHub Actions run
   [40368689838](https://github.com/alexodas/TruncatedSieveFlux/actions/runs/40368689838):
   - `TruncatedSieveFluxComparator.gcd_covariance`
   - `TruncatedSieveFluxComparator.second_moment_gcd`
   - `TruncatedSieveFluxComparator.fourth_moment_quartic`
   - `TruncatedSieveFluxComparator.fourth_moment_le_variance`
   - `TruncatedSieveFluxComparator.fourth_moment_cubic_conditional`

The last theorem **assumes** a linear variance bound. It is not an
unconditional cubic estimate. No `O(B²)` fourth-moment theorem is proved.

The independent kernel export includes the definitions and proofs needed
by the compared statements. An auxiliary theorem not in their proof
dependency closure is **not** thereby independently checked by Comparator.

## Why not one file per internal lemma?

A Palomar Challenge must state the claim independently of all non-allowlisted
repository code. In particular, it cannot simply import
`FourthMomentResearch`, and it has a strict 1,000-line / 100 KiB limit.
A Solution may use the project research proofs, but its independently
stated definitions must agree with the Challenge declarations.
One auditable Challenge/Solution pair can include several related
theorems; creating a file for each internal helper is not required
or automatically safer.

As of the snapshot from which this PR was branched, the source
`FourthMomentResearch.lean` has **78** top-level `theorem`
declarations (of which **12** are `private`), counted syntactically.
Those declarations are not all separately listed in a Comparator JSON
configuration. Covering every statement as an individual Comparator
challenge is a *further formalization and review project*, rather than
something achieved merely by adding the five headline theorem wrappers.

For future additions, expand the independent Challenge/Solution pair
or create a new pair and config, keep definitions mathematically
non-vacuous and Challenge imports limited to permitted libraries,
and require **actual successful CI logs** before marking a theorem
Comparator-verified.

## Running the checks

```sh
lake exe cache get
lake build Challenge Solution FourthMomentResearch CovarianceChallenge CovarianceSolution
lake env leanchecker Solution
lake env leanchecker FourthMomentResearch
lake env leanchecker CovarianceSolution
bash scripts/check.sh comparator.json
bash scripts/check.sh comparator-covariance.json
```

The Comparator checks require the Linux sandbox and the configured
external kernel binaries. Each `comparator*.json` path represents
a separate Palomar configuration and submission entry, even when
both are submitted against the same pinned commit.
