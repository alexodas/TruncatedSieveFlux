# Fourth-moment research program for Möbius rounding errors

**Status: open research target; no fourth-moment `O(B^2)` proof.**

## Central question

Study the periodic signed rounding error

```text
E_B(M) = sum_{1 ≤ d ≤ B} mu(d) * ((M mod d)/d).
```

With `L_B = lcm(1,...,B)` and its period mean `mean_B`, seek an
absolute constant `C4` such that

```text
(1/L_B) * sum_{0 ≤ M < L_B} (E_B(M)-mean_B)^4 ≤ C4*B^2.
```

The proposed positive-density oscillation consequences would require
additional work beyond the identity and finite-sum bounds established
here. Neither the target inequality nor any claim of originality is proved.

## Most useful exact formulas already proved

**Common period and mean.** For any `T > 0` divisible by every
`1 ≤ d ≤ B`, Lean proves

```text
E_B(M+T) = E_B(M),
(1/T) * sum_{0 ≤ M < T} E_B(M)
    = sum_{1 ≤ d ≤ B} mu(d) * (d-1)/(2*d),
E_B(M) - mean_(B,T)
    = sum_{1 ≤ d ≤ B} mu(d) * ((M mod d)/d - (d-1)/(2*d)).
```

**Pairwise correlations.** The newly formalized
`empiricalSecondMoment_eq_covariance_sum` theorem writes the centered
second moment as the exact Möbius-weighted quadratic form in the modular
covariances. The supporting `empiricalSecondMoment_eq_pairwise_sum`
identity expands it over ordered pairs; `empiricalSecondMoment_nonneg`
proves positivity and `empiricalModularCovariance_comm` proves symmetry.

The incremental gcd-covariance formalization also establishes the boundary case `a = 1`: `centeredModularFraction m 1 H = 0`, hence `empiricalModularCovariance 1 b H = 0` and (by symmetry) `empiricalModularCovariance a 1 H = 0` for every `H`. This agrees with the gcd formula because `gcd(1,b)=1`. The new `centeredModularFraction_common_period` lemma furthermore rewrites each centered summand on any positive multiple of its modulus as `(m mod d)/d - (d-1)/(2*d)`, independent of the chosen averaging period. The follow-up `empiricalModularCovariance_common_period_explicit` combines two instances of that normal form into an exact finite sum over any positive common period. The supporting `centeredModularFraction_mul_add_common_period` proves that the product of the two centered modular fractions is itself periodic under any positive common period (with that period used for centering). The new `empiricalModularCovariance_lcm_explicit` specializes the exact finite covariance sum to `lcm(a,b)` for positive `a,b`. The new `empiricalModularCovariance_eq_lcm` is the full **period-independence theorem**: for positive `a,b` and every positive common multiple `T`, `C_(a,b;T) = C_(a,b;lcm(a,b))`. Its proof formalizes the summation of any real-valued periodic sequence over `q` full cycles. The corollary `empiricalModularCovariance_diagonal_common_period` upgrades the exact diagonal formula to every positive multiple of `d`. The remaining arithmetic task is to evaluate the off-diagonal sum on the lcm via the gcd of the moduli. The additional `two_mul_empiricalModularCovariance_le_diagonal` inequality proves `2*C_(a,b;H) ≤ C_(a,a;H)+C_(b,b;H)` for every `H>0`, using a pointwise square inequality. The new complementary lemma `neg_diagonal_le_two_mul_empiricalModularCovariance` gives `-(C_(a,a;H)+C_(b,b;H)) ≤ 2*C_(a,b;H)` by the square of the *sum* of the centered fractions. Taken together these are two-sided bounds. They are general structural constraints, not the expected exact gcd evaluation, and does not settle the general off-diagonal case.

For the diagonal over a full modulus, the proved identity is

```text
(1/d) * sum_{0 ≤ M < d} ((M mod d)/d - (d-1)/(2*d))^2
   = (d^2-1)/(12*d^2)   for d>0.
```

**Full-period moment invariance (new formalization).** The new Lean theorems `empiricalSecondMoment_eq_of_common_periods` and `empiricalFourthMoment_eq_of_common_periods` respectively identify the entire variance and the entire centered fourth moment on any two positive periods divisible by every `1 ≤ d ≤ B`. The second-moment theorem combines the Möbius quadratic-form identity with `empiricalModularCovariance_eq_lcm`; the fourth-moment theorem sums the periodic centered fourth power over repeated cycles and compares periods through their least common multiple. Both moment-invariance proof scripts have passed the GitHub Actions Lean `verify` compilation; the separate independent-kernel Comparator checks the Challenge/Solution theorem. Their conclusions are exact period-independence identities, **not** the conjectured `O(B²)` bound.

**Four-divisor correlations.**
`empiricalFourthMoment_eq_fourfold_sum` expands the full empirical
fourth moment into products of four centered modular fractions.
These expansions are exact, but do not establish cancellation.

## Supporting formalization

The `Solution.lean` module supplies the finite Möbius divisor-sieve
identity and the quotient/remainder bound. The sole Palomar Comparator
theorem, `moebius_log_cutoff_residual_approximation`, bounds the
residual-rounding discrepancy by the integer cutoff. Auxiliary
lemmas prove the modular mean over any number of full periods,
the rational remainder representation, and the unconditional
`16 B^4` centered fourth-moment bound.

## Quantitative reduction and an O(B³) paper argument

On any positive common period `T`, the following are **proved in Lean**:
`abs_centered_roundingError_common_period_le_half`,
`empiricalFourthMoment_le_secondMoment_mul`,
`empiricalFourthMoment_le_half_quartic`, and
`empiricalFourthMoment_le_cubic_of_variance_le`.

```text
|E_B(M) - mean_(B,T)| ≤ B/2
fourth_(B,T) ≤ (B²/4) * V_(B,T)
fourth_(B,T) ≤ B⁴/16
V_(B,T) ≤ C*B  ==>  fourth_(B,T) ≤ (C/4)*B³
```

The cubic Lean theorem **assumes** the stated variance bound.
That assumption is not yet proved in Lean.

A **separate paper-level derivation**, not yet machine-checked,
uses the classical finite-period covariance formula

```text
Cov((M mod a)/a, (M mod b)/b)
    = (gcd(a,b)² - 1)/(12*a*b).
```

By the Möbius coefficient bound `|mu(d)| ≤ 1`,

```text
V_B ≤ (1/12) * sum_{1 ≤ a,b ≤ B} gcd(a,b)²/(a*b).
```

Write `a=g*r`, `b=g*s`, with `g=gcd(a,b)`. Dropping
the coprimality restriction on `r,s`, and counting possible
positive `g`, gives

```text
sum_{1 ≤ a,b ≤ B} gcd(a,b)²/(a*b)
  ≤ B * sum_{r,s ≥ 1} 1/(r*s*max(r,s))
  ≤ B * (sum_{n ≥ 1} n^(-3/2))²
  ≤ 9B.
```

The last bound follows from
`sum_{n ≥ 1} n^(-3/2) ≤ 1 + integral_1^infty x^(-3/2) dx = 3`.
Hence, on every positive common period,

```text
V_B ≤ 3B/4
fourth_(B,T) ≤ (B²/4)*V_B ≤ 3B³/16.
```

**Verification status:** the gcd covariance identity and final
unconditional cubic estimate have *not* yet been proved in Lean.
The covariance identity is classical; see for example
https://math.stackexchange.com/questions/140499/a-sum-of-fractional-parts .
The paper-level estimate should be independently reviewed.
No claim of originality is made.

**Divisibility family (new Lean proof submitted, CI pending).** The auxiliary `centeredModularFraction_sum_self_zero` and `sum_range_mul_index_of_period_zero_mean` formalize zero centering and index-weighted periodic averaging. The proposed `empiricalModularCovariance_dvd_right_base` identifies `C_(a,b;b) = (a/b) C_(a,a;a)` when `a ∣ b`; `empiricalModularCovariance_gcd_of_dvd` would then yield `(gcd(a,b)^2-1)/(12ab)` on every positive period divisible by `b`. This is a proper off-diagonal infinite family when `a < b`, but **its Lean proof is still being checked in CI**. The corollaries `empiricalModularCovariance_gcd_of_dvd_left` and `empiricalModularCovariance_gcd_of_comparable` extend the pending proof by symmetry to all positive moduli comparable under divisibility. A further proposed Lean theorem, `empiricalModularCovariance_gcd_two_odd`, covers the non-comparable pairs `(2,b)` for odd `b`, showing zero covariance by exact cancellation of the two b-blocks in `2*b`. The new source contains explicit lemmas for the sign reversal of the centered fraction mod 2 and the periodicity mod b. The first odd-modulus proof has passed Lean `verify`. The new `empiricalModularCovariance_gcd_two_any` combines even b via divisibility and odd b via cancellation, giving the gcd formula for **every b>0** with first modulus two; `empiricalModularCovariance_gcd_any_two` handles the symmetric family. Both corollaries have passed the GitHub Actions Lean `verify` job. The independent-kernel Comparator job applies to the separate Challenge/Solution theorem. The next candidate `empiricalModularCovariance_gcd_three_coprime` treats all pairs `(3,b)` with `b % 3 ≠ 0`, via the exact three-block cancellation identity `centeredModularFraction_three_block_sum_zero` and `empiricalModularCovariance_three_coprime_product_zero`. Its Lean compilation has **succeeded** (GitHub Actions commit `b6a0810`). Additional corollaries `empiricalModularCovariance_gcd_three_any` and `empiricalModularCovariance_gcd_any_three` combine the coprime cancellation with the divisibility case to target all positive pairs with a modulus equal to three. The complete workflow, including the separate Challenge/Solution Comparator job, succeeded on the corrected proof commit. This expands the range of test cases but does not prove the general gcd covariance formula.

**General CRT mechanism (new, CI pending).** Rather than treating
additional moduli individually, `coprime_zmod_product_sum_factorization`
applies Mathlib's Chinese remainder equivalence to factor a full product
correlation into the product of two independent residue sums, for
**any coprime moduli**. The lemma
`coprime_zmod_centered_orthogonality` makes zero mean imply zero
correlation. The accompanying `centered_zmod_residue_sum_zero` and
`coprime_zmod_centered_residue_product_zero` apply this algebra to
centered rational fractional parts, still indexed by `ZMod`.

**Status:** the initial CRT factorization and centered ZMod correlation have passed Lean CI. The newly proposed `coprime_zmod_chineseRemainder_nat_coordinates` and `coprime_centered_modular_sum_zero` connect those algebraic identities to natural-number range sums, and `empiricalModularCovariance_gcd_coprime` asserts the exact gcd formula for **all coprime positive moduli** on any positive common period. These newest theorems still await CI validation. The general non-coprime off-diagonal case remains open. No improvement to the unconditional fourth-moment bound is asserted.

## What must be proved next

The current file has **not** evaluated the off-diagonal modular
covariance for arbitrary `a,b` over a full common period.
The expected classical gcd-based formula is

```text
Cov((M mod a)/a, (M mod b)/b)
   = (gcd(a,b)^2 - 1)/(12*a*b).
```

That formula should be formalized and checked independently before
it is used to derive a closed expression for the full variance.
Even a verified second-moment identity would not by itself prove
the `O(B^2)` fourth-moment target: the four-variable correlations
remain the substantive analytic obstacle.

## Literature and originality

Closely related high moments and truncations occur in Granville,
Koukoulopoulos and Maynard, *Sieve weights and their smoothings*
(2016 preprint; later publication):
https://arxiv.org/abs/1606.06781.
Existing fractional-part and gcd-covariance identities also overlap
with this area. Novelty requires a substantive mathematical and
bibliographic review rather than a successful Lean compilation.
