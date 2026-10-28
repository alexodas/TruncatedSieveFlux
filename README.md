# Periodic Möbius rounding error — Lean 4 / Mathlib

[![Zenodo DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23736533.svg)](https://doi.org/10.5281/zenodo.23736533)

This repository formalizes **exact periodic moments** of a truncated Möbius
rounding error and develops a route toward a genuinely stronger oscillation
theorem. The main research target is **open**; the verified finite identities
are structural reductions, not yet a new asymptotic result.

## Outstanding research question — not yet proved

For integers `B ≥ 2` and `M ≥ 0`, define

```text
E_B(M) = sum_{1 ≤ d ≤ B} mu(d) * ((M mod d) / d),
L_B = lcm(1, ..., B),
mean_B = (1/L_B) * sum_{0 ≤ M < L_B} E_B(M).
```

Does there exist a constant `C4 > 0`, independent of `B`, such that

```text
(1/L_B) * sum_{0 ≤ M < L_B} (E_B(M) - mean_B)^4 ≤ C4 * B^2
```

for all `B ≥ 2`? Establishing this bound could support quantitative
results about the frequency of large oscillations. **Neither the bound
nor those consequences have been proved, and no originality claim is made.**

## Main results actually verified in Lean

**Exact periodicity and centering.** Every positive common multiple
`T` of `1,...,B` is a period of `E_B`, and its mean is exactly

```text
E_B(M + T) = E_B(M),
mean_(B,T) = sum_{1 ≤ d ≤ B} mu(d) * (d - 1)/(2*d),
E_B(M) - mean_(B,T)
  = sum_{1 ≤ d ≤ B} mu(d) * ((M mod d)/d - (d - 1)/(2*d)).
```

In particular `T = B!` works. These statements have been proved for
arbitrary positive common periods, not only for a sample of integers.

**Second moment: reduction to pair correlations.** Define

```text
r_(d,H)(M) = (M mod d)/d
             - (1/H) * sum_{0 ≤ n < H} (n mod d)/d,
V_(B,H) = (1/H) * sum_{0 ≤ M < H} (E_B(M)-mean_(B,H))^2.
```

Lean proves that `V_(B,H)` is nonnegative and expands exactly into
the double sum of weighted pair correlations:

```text
V_(B,H) = (1/H) * sum_{0 ≤ M < H} sum_{1 ≤ a,b ≤ B}
  mu(a)*mu(b)*r_(a,H)(M)*r_(b,H)(M).
```

Equivalently, with

```text
C_(a,b;H) = (1/H) * sum_{0 ≤ M < H} r_(a,H)(M) * r_(b,H)(M),
```

Lean proves the exact quadratic-form identity

```text
V_(B,H) = sum_{1 ≤ a,b ≤ B} mu(a)*mu(b)*C_(a,b;H).
```

**General gcd covariance — proved in Lean.** The theorem
`empiricalModularCovariance_gcd_general` establishes, for every
positive `a,b,T` with `a ∣ T` and `b ∣ T`:

```text
C_(a,b;T) = (gcd(a,b)^2 - 1)/(12*a*b).
```

There is **no coprimality or divisibility assumption between a and b**.
The proof uses the positive gcd `g`, the coprime quotients
`r=a/g`, `s=b/g`, an exact decomposition into `g` residue
fibers, CRT cancellation of the reduced correlations, and the
previously formalized diagonal covariance of `g`.
The precise theorems are `gcd_fiber_mod`,
`centered_residue_on_gcd_fiber`,
`coprime_centered_shifted_product_sum`,
`empiricalModularCovariance_mul_coprime`, and
`empiricalModularCovariance_gcd_general`. The full gcd proof
passed the GitHub Actions Lean `verify` job on commit `0bfbf58`.

**Mathematical provenance:** Robert Israel's answer to Eric Naslund,
["A sum of fractional parts" (2012)](https://math.stackexchange.com/questions/140499/a-sum-of-fractional-parts),
gives the classical uncentered two-modulus product formula. The
covariance formula above is its centered and period-normalized
version, with a separate Lean proof using CRT and gcd fibers.
This source and its relationship are recorded in `formalization.yaml`;
the formalization does **not** claim to discover the identity or
establish research-paper-level novelty.

The additional theorem `empiricalSecondMoment_eq_gcd_sum`
now makes the entire Möbius-weighted second moment an **explicit
finite gcd quadratic form**:

```text
V_(B,T) = sum_{1 ≤ a,b ≤ B} mu(a)*mu(b)*
          (gcd(a,b)^2 - 1)/(12*a*b)
```

for every positive common period `T` of `1,…,B`.
This exact identity is proved in Lean and its corresponding
independently stated result has **also passed Comparator**
with NanoDa and con-ron (see below). The quantitative upper bound
`V_(B,T) ≤ 3B/4` from the paper-level argument is **not**
yet formalized. Supporting lemmas are checked by Lean and those
needed by compared proofs are covered as dependencies, but not
all have separate Comparator Challenge statements.

**Period invariance.** Lean also proves that any two positive
common averaging periods give the same variance and the same
centered fourth moment, via
`empiricalSecondMoment_eq_of_common_periods` and
`empiricalFourthMoment_eq_of_common_periods`.
These exact identities do **not** establish the desired
`O(B²)` fourth-moment bound.

The diagonal covariance for a complete modulus is also formalized:

```text
(1/d) * sum_{0 ≤ M < d} (M/d - (d-1)/(2*d))^2
   = (d^2 - 1)/(12*d^2)    (d ≥ 1).
```

**Fourth moment: exact correlation expansion.** The analogous
four-index expansion is verified in Lean. It reduces the problem to
four-way arithmetic correlations; it does **not** bound their total
contribution by `O(B^2)`.

See [FOURTH_MOMENT_RESEARCH.md](FOURTH_MOMENT_RESEARCH.md) for the
precise open problem, mathematical obstacles, and proof status.

## A quantitative reduction (partially formalized)

For every positive common period `T`, **Lean has proved** the
pointwise and moment estimates

```text
|E_B(M) - mean_(B,T)| ≤ B/2,
fourth_(B,T) ≤ (B²/4) * V_(B,T),
fourth_(B,T) ≤ B⁴/16.
```

It also proves the conditional implication

```text
V_(B,T) ≤ C*B  ==>  fourth_(B,T) ≤ (C/4)*B³.
```

**Mathematical derivation, not yet fully in Lean:** combining the
**now Lean-verified** full gcd-based covariance formula for rational
fractional parts with a **not-yet-formalized** divisor-sum bound gives `V_(B,T) ≤ 3B/4`,
hence `fourth_(B,T) ≤ 3B³/16`. This is a genuine exponent
improvement from 4 to 3, but appears elementary and is **not claimed
as a novel mathematical result**. The covariance formula is formally proved; only
the arithmetic bound and its consequences still need formalization in Lean.

The detailed argument and precise verification status appear in
[FOURTH_MOMENT_RESEARCH.md](FOURTH_MOMENT_RESEARCH.md).

### CRT and gcd-fiber method

For coprime `r,s`, Mathlib's Chinese remainder equivalence
`ZMod (r*s) ≃ ZMod r × ZMod s` factors every full-period
product correlation into separate residue sums.
The theorem `coprime_centered_modular_sum_zero` transfers that
cancellation to the natural-number indexing used here.

For arbitrary original moduli, factoring out `g=gcd(a,b)`
leaves just such a coprime pair. On `m=k*g+t`,
the centered fraction becomes its reduced-modulus counterpart
plus `(t-(g-1)/2)/(g*r)`. The mixed terms vanish under CRT,
and the remaining sum is the variance of residues modulo `g`.
The general theorem and the exact finite gcd variance formula are
Lean-verified; **the unconditional cubic and conjectured quadratic
fourth-moment bounds remain open formalization tasks**.

## Supporting lemmas and the finite-sieve theorem

The file `FourthMomentResearch.lean` also proves the exact rational
remainder representation, mean over complete modular periods,
and elementary uniform bounds. For an **arbitrary nonempty
averaging interval** the coarse estimate is

```text
|E_B(M)| ≤ B,
fourth_(B,H) ≤ 16*B^4    (H ≥ 1).
```

On **positive common periods**, the stronger verified estimate
`fourth_(B,T) ≤ B^4/16` applies, as stated above. Neither is
the conjectured `O(B²)` bound.

The `Challenge.lean` / `Solution.lean` pair has **one** submitted
Comparator theorem, `moebius_log_cutoff_residual_approximation`.
It links the periodic error to the omitted signed divisor mass of the
logarithmically truncated sieve: for `x ≥ 2`,
`B = 1+ceil((log x)^4)` and `M=ceil(x)-1`,

```text
|R(B,x) - 1 + M * sum_{1 ≤ d ≤ B} mu(d)/d| ≤ B.
```

This is a supporting **finite** approximation, not an asymptotic
cancellation theorem. It is not the claimed resolution of the open
fourth-moment question.

## Independent Comparator checks for the principal research results

A second independent statement/solution pair is provided:
`CovarianceChallenge.lean` defines fractional-part covariance and
the centered Möbius second moment **directly from Mathlib**, without
importing the project research proofs. `CovarianceSolution.lean`
supplies proofs by bridging those identical definitions to
`FourthMomentResearch.lean`.

The separate `comparator-covariance.json` explicitly selects **five**
research declarations:

- `TruncatedSieveFluxComparator.gcd_covariance` — exact covariance
  `(gcd(a,b)^2-1)/(12ab)` for all positive a,b and common periods.
- `TruncatedSieveFluxComparator.second_moment_gcd` — the complete
  finite Möbius-weighted gcd quadratic form for the second moment.
- `TruncatedSieveFluxComparator.fourth_moment_quartic` — the
  unconditional `B⁴/16` elementary estimate on common periods.
- `TruncatedSieveFluxComparator.fourth_moment_le_variance` — the
  fourth-to-second-moment inequality.
- `TruncatedSieveFluxComparator.fourth_moment_cubic_conditional` —
  the cubic estimate **assuming** a linear variance bound, not
  an unconditional cubic theorem.

All **five** selected research claims have passed Comparator
with independent NanoDa and con-ron kernel checks, as confirmed
by [GitHub Actions run 40368689838](https://github.com/alexodas/TruncatedSieveFlux/actions/runs/40368689838).
The original `comparator.json` continues to check **only**
the finite cutoff-sieve theorem. The two configurations can be submitted
**separately** to Palomar using the same full commit SHA; each
configuration corresponds to a separate registry entry.

**Coverage limit:** the independent kernels also check the
proof dependencies used by the selected research theorems.
The CI additionally runs `leanchecker` over each completed project
module, replaying **all** of its local proof declarations with
Lean's kernel. That module-wide replay is not a distinct kernel
implementation, and other theorems in `FourthMomentResearch.lean`
are **not automatically added as named Comparator claims**. There are multiple independent
supporting lemmas and not every Lean declaration is currently a
separate Challenge theorem. Adding all of them would require
additional auditable Challenge/Solution statements or other dedicated
configs; it would be misleading to claim 100% named-theorem coverage.
The explicit coverage inventory is in
[COMPARATOR_COVERAGE.md](COMPARATOR_COVERAGE.md).

For local use (Linux with bubblewrap and supported kernel binaries):

```sh
lake exe cache get
lake build Challenge Solution FourthMomentResearch CovarianceChallenge CovarianceSolution
bash scripts/check.sh comparator.json
bash scripts/check.sh comparator-covariance.json
```

## Checking the proofs

`Challenge.lean` contains **one intentional `sorry`**,
and `CovarianceChallenge.lean` contains **five intentional
`sorry` statements**: each one is a statement placeholder
for a Comparator challenge. The completed proof modules
`Solution.lean`, `FourthMomentResearch.lean`, and
`CovarianceSolution.lean` have **no `sorry`**. Accordingly,
`formalization.yaml` reports `status.sorry_count: 0`,
excluding the deliberate placeholders in both Challenge modules.

**Important submission scope:** the original `comparator.json`
selects **only** `TruncatedSieveFlux.moebius_log_cutoff_residual_approximation`
from `Challenge`/`Solution`. The separate
`comparator-covariance.json` selects **five** research statements
from `CovarianceChallenge`/`CovarianceSolution`, including the
general gcd covariance and exact second moment. Both configurations
have passed Comparator with independent kernels. To substantiate a
particular result in Palomar, submit the corresponding configuration;
passing one does not imply that the other was submitted.

```sh
lake exe cache get
lake build Challenge Solution FourthMomentResearch
bash scripts/check.sh comparator.json
bash scripts/check.sh comparator-covariance.json
```

For a Palomar submission, use the public repository
`alexodas/TruncatedSieveFlux` and the **full 40-character SHA
of the commit being submitted**. Select the repository-relative
configuration path `comparator.json` for the finite-sieve theorem,
or `comparator-covariance.json` for the five research results.
The metadata path is `formalization.yaml`. A branch name or
short SHA is not a substitute for a pinned full commit identifier.
Running Comparator locally also requires the independent-kernel
tooling. These are two separate Comparator configurations; the
five research claims **already have** their own Challenge/Solution
interface and a successful independent-kernel comparison.

## Next steps: formal verification and research milestones

The five research Comparator statements are independently checked, but
**machine verification is not by itself evidence of research novelty**.
The automated Palomar review accepted the mechanical checks while finding
that the present results had not been shown to merit a research paper or
serious note. The next stages therefore separate new Lean proofs from a
substantive mathematical contribution:

1. **Formalize the linear variance bound.** Starting from the exact
   gcd-weighted quadratic formula, verify the finite inequality
   `∑_{1≤a,b≤B} gcd(a,b)^2/(a*b) ≤ 9*B` for positive `B`,
   yielding `V_(B,T) ≤ 3*B/4` on every positive common period.
   Combine this with the existing conditional moment inequality to
   prove `fourth_(B,T) ≤ 3*B³/16` in Lean. These are **planned
   proofs**, not currently established Lean results, and the
   argument appears elementary rather than novel.
2. **Investigate genuine fourth-order cancellation.** Use the existing
   fourfold expansion and period invariance to study correlations
   of four modular fractional parts weighted by Möbius coefficients.
   Identify a rigorously testable estimate that improves on the
   quartic/cubic bounds and, ultimately, could support the open
   `O(B²)` fourth-moment target. A second-moment identity alone
   does not prove such cancellation.
3. **Audit provenance and mathematical significance.** Compare
   the precise proposed estimate against published work on sieve
   weights, fractional parts and gcd correlations; state exactly
   which result is classical, a formalization, an elementary
   consequence or potentially new. Seek independent human
   mathematical review before claiming research-paper-level interest.
4. **Extend formal and independent verification where useful.**
   Check each new Lean theorem with CI, complete-module `leanchecker`,
   and a suitable independent Comparator Challenge/Solution pair.
   Keep an explicit [coverage inventory](COMPARATOR_COVERAGE.md);
   do not label supporting lemmas as individually compared unless
   they were actually selected.
5. **Reassess Palomar submission only after substantive progress.**
   Correct source attribution and Challenge documentation are
   necessary, but **do not resolve the review's interest objection**.
   Resubmit a pinned commit only when a meaningful, well-sourced
   contribution can be justified honestly. Another mechanically
   successful check is not sufficient on its own.

The mathematical reductions and unresolved obstacles are detailed
in [FOURTH_MOMENT_RESEARCH.md](FOURTH_MOMENT_RESEARCH.md)
under **What must be proved next**.

## Archived releases and citation

This evolving research-software project is archived on Zenodo.

- **All-versions (concept) DOI:** [10.5281/zenodo.23736533](https://doi.org/10.5281/zenodo.23736533).
- **First archived release:** [v0.1.0](https://github.com/alexodas/TruncatedSieveFlux/releases/tag/v0.1.0).

The concept DOI identifies the project across versions. When citing a particular
version, use the **version-specific DOI** shown on that version's Zenodo record
so readers can identify the exact archived snapshot. See
[CITATION.cff](CITATION.cff) for software citation metadata.

## Authorship, experimental context, and limitations

**Human experimenter and repository maintainer:** Alessandro Odasso.

**AI system used for mathematical exploration and formalization:** OpenAI GPT-6 series.

This repository documents an experiment in the use of large language models
(LLMs) for scientific and mathematical research. Alessandro Odasso is **not a
professional mathematician**; his interest here is in exploring what LLMs
can achieve in mathematical research when combined with formal proof tools.
He initiated and directed the experiment and maintains the public repository.
The GPT-6 series performed substantial mathematical exploration, Lean proof
construction, code development, debugging, and iterative verification under
that human direction.

The human experimenter **cannot independently guarantee the mathematical
correctness, originality, or significance** of the results. The evidence for
technical correctness consists of successful Lean compilation and kernel
checks of the completed proof modules, together with the documented
Comparator checks for selected statements. These checks support the
formal validity of the Lean theorems within their stated assumptions and
trusted foundations; they do **not** establish that the formal statements
capture every intended informal claim, that a result is new, or that it is
mathematically important. The precise scope of independent statement
comparison is described in [COMPARATOR_COVERAGE.md](COMPARATOR_COVERAGE.md).

This work is shared openly for transparency and reproducibility. Interested
mathematicians and formal-methods researchers are invited to examine,
critique, reproduce, correct, or extend the results. **Independent expert
mathematical review has not yet been performed.** The proposed stronger
fourth-moment bound remains an open research target, not a theorem proved
by this repository.

Project metadata: [formalization.yaml](formalization.yaml).
License: Apache-2.0.
