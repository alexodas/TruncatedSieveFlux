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

**This does not yet evaluate general off-diagonal terms** `a ≠ b`. The dedicated gcd-covariance branch begins with the modulus-one boundary case, in which the centered modular fraction and all associated covariances vanish. An additional pointwise lemma, `centeredModularFraction_common_period`, rewrites the centered modular fraction explicitly on **every positive multiple** of its modulus. This supplies a period-independent normal form for the future gcd calculation. The new theorem `empiricalModularCovariance_common_period_explicit` now rewrites the entire covariance, for arbitrary positive moduli on any positive common period, as a finite product sum of those explicit centered residues. This is a reduction, not an evaluation of that sum. A further general covariance inequality is now included: for every nonempty averaging interval, `2*C_(a,b;H) ≤ C_(a,a;H) + C_(b,b;H)`, from the nonnegative square of the difference of centered fractions. The complementary lower bound `-(C_(a,a;H)+C_(b,b;H)) ≤ 2*C_(a,b;H)` is now also proposed, yielding a two-sided quadratic control. These inequalities do not evaluate the off-diagonal covariance or establish the linear variance bound. A new supporting periodicity lemma, `centeredModularFraction_mul_add_common_period`, also records invariance of the product of the two centered modular fractions under translation by a common period. This is a preparatory statement for reducing covariance sums to least common periods; the new `empiricalModularCovariance_lcm_explicit` specializes the exact centered product sum to the least common period `lcm(a,b)` for positive moduli. The new theorem `empiricalModularCovariance_eq_lcm` **does** prove that the covariance on any positive common period agrees with the covariance on `lcm(a,b)`; its proof repeats a periodic finite sum and cancels the number of periods. Consequently, `empiricalModularCovariance_diagonal_common_period` extends the exact diagonal formula `(d²-1)/(12d²)` to **every positive multiple** of `d`. This is a substantive period-independence theorem, but the general off-diagonal gcd evaluation remains open in Lean.

**Full-moment period invariance (new in PR #6).** The theorem `empiricalSecondMoment_eq_of_common_periods` lifts the covariance identity to the entire Möbius-weighted variance: if `T` and `U` are positive common multiples of all `1,…,B`, then `V_(B,T) = V_(B,U)`. A second, independent periodic-sum argument gives `empiricalFourthMoment_eq_of_common_periods`, proving `fourth_(B,T) = fourth_(B,U)` for the same periods. These theorems identify the exact moments across different choices of complete averaging period; they are **not** improved upper bounds and do not prove the general off-diagonal gcd formula. Both moment-invariance proof scripts have passed the GitHub Actions Lean `verify` compilation; the independent Comparator job pertains to the separate Challenge/Solution theorem.

**Divisible-modulus gcd covariance (new proof under CI review).** Two new Lean scripts, `empiricalModularCovariance_dvd_right_base` and `empiricalModularCovariance_gcd_of_dvd`, target the first genuinely non-diagonal family. If `a > 0`, `b > 0`, `a ∣ b`, and `T > 0` is a multiple of `b`, the proposed identity is `C_(a,b;T) = (gcd(a,b)^2-1)/(12*a*b)`. The argument reduces this to `(a/b)*C_(a,a;a)` by periodic zero-mean weighted sums. **Do not treat this new family as verified until the latest GitHub Actions Lean build passes.** By covariance symmetry, `empiricalModularCovariance_gcd_of_dvd_left` and `empiricalModularCovariance_gcd_of_comparable` extend this proposed exact formula to every pair with `a ∣ b` **or** `b ∣ a`. The general case where neither modulus divides the other remains open.

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
classical gcd-based covariance formula for rational fractional parts
with an elementary divisor-sum bound gives `V_(B,T) ≤ 3B/4`,
hence `fourth_(B,T) ≤ 3B³/16`. This is a genuine exponent
improvement from 4 to 3, but appears elementary and is **not claimed
as a novel mathematical result**. The full covariance formula and
the arithmetic bound still need formalization in Lean.

The detailed argument and precise verification status appear in
[FOURTH_MOMENT_RESEARCH.md](FOURTH_MOMENT_RESEARCH.md).

## Supporting lemmas and the finite-sieve theorem

The file `FourthMomentResearch.lean` also proves the exact rational
remainder representation, mean over complete modular periods,
elementary uniform bounds, and the coarse fourth-moment bound

```text
|E_B(M)| ≤ B,
fourth_(B,H) ≤ 16*B^4    (H ≥ 1).
```

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

`Challenge.lean` contains one **intentional** `sorry` for the challenge
statement. `Solution.lean` and `FourthMomentResearch.lean` contain
no `sorry`. The CI builds all three Lean modules; Comparator compares
the one Challenge/Solution theorem with Lean, NanoDa and con-ron.
The research lemmas are compiled by Lean, but are not separately listed
as Comparator challenge theorems.

```sh
lake exe cache get
lake build Challenge Solution FourthMomentResearch
bash scripts/check.sh
```

Running Comparator also requires `bwrap` and its independent kernels.

## Authorship and transparent AI assistance

**Author and responsible maintainer:** Alessandro Odasso.

ChatGPT **GPT-6 with High thinking effort** (as reported by the
contributor) assisted with mathematical exploration, proof drafting,
debugging, and repository verification. The project was human-directed
and AI-assisted. Formal verification establishes correctness of the
Lean statements actually proved; it does not establish mathematical
originality or replace independent mathematical review.

Project metadata: [formalization.yaml](formalization.yaml).
License: Apache-2.0.
