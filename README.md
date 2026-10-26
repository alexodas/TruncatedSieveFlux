# Periodic Möbius rounding error — Lean 4 / Mathlib

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

The additional theorem `empiricalSecondMoment_eq_gcd_sum`
now makes the entire Möbius-weighted second moment an **explicit
finite gcd quadratic form**:

```text
V_(B,T) = sum_{1 ≤ a,b ≤ B} mu(a)*mu(b)*
          (gcd(a,b)^2 - 1)/(12*a*b)
```

for every positive common period `T` of `1,…,B`.
This exact identity is proved in Lean; the quantitative upper bound
`V_(B,T) ≤ 3B/4` from the paper-level argument is **not**
yet formalized. The research lemmas are Lean-compiled, not
independently checked by Palomar Comparator.

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

## Checking the proofs

`Challenge.lean` contains **one deliberate `sorry`**, as required
for the statement to be proved by the Comparator. The completed
proof modules `Solution.lean` and `FourthMomentResearch.lean`
contain **zero `sorry`**. This is why `formalization.yaml`
reports `status.sorry_count: 0`: following the Palomar template,
the count excludes the intentional Challenge placeholder.

**Important submission scope:** `comparator.json` selects **only**
`TruncatedSieveFlux.moebius_log_cutoff_residual_approximation`
from the `Challenge`/`Solution` pair. The general gcd-covariance
theorem and exact second-moment formula are already **proved by Lean**
in `FourthMomentResearch.lean`, but they are **not part of the
Comparator submission**. Passing Comparator with the present
configuration does **not** amount to an independent-kernel
comparison of those research theorems.

```sh
lake exe cache get
lake build Challenge Solution FourthMomentResearch
bash scripts/check.sh
```

For a Palomar submission, use the public repository
`alexodas/TruncatedSieveFlux`, the **full 40-character SHA of the
commit being submitted**, and the repository-relative Comparator
configuration path `comparator.json`. The conventional metadata
path is `formalization.yaml`. A branch name or short SHA is not
a substitute for the full commit identifier. Running Comparator
locally also requires the configured independent-kernel tooling.

To submit the **general gcd covariance itself** to Comparator in
a future iteration, the corresponding statement must first be
exposed in the Challenge/Solution comparison interface and listed
in `comparator.json`; documentation changes alone cannot do that.

## Authorship and transparent AI assistance

**Author and responsible maintainer:** Alessandro Odasso.

ChatGPT **GPT-6** assisted with mathematical exploration,
proof drafting, debugging, and repository verification. The project was human-directed
and AI-assisted. Formal verification establishes correctness of the
Lean statements actually proved; it does not establish mathematical
originality or replace independent mathematical review.

Project metadata: [formalization.yaml](formalization.yaml).
License: Apache-2.0.
