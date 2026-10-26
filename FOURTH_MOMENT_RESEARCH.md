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

**Divisibility family (new Lean proof submitted, CI pending).** The auxiliary `centeredModularFraction_sum_self_zero` and `sum_range_mul_index_of_period_zero_mean` formalize zero centering and index-weighted periodic averaging. The proposed `empiricalModularCovariance_dvd_right_base` identifies `C_(a,b;b) = (a/b) C_(a,a;a)` when `a ∣ b`; `empiricalModularCovariance_gcd_of_dvd` would then yield `(gcd(a,b)^2-1)/(12ab)` on every positive period divisible by `b`. This is a proper off-diagonal infinite family when `a < b`, but **its Lean proof is still being checked in CI**. The corollaries `empiricalModularCovariance_gcd_of_dvd_left` and `empiricalModularCovariance_gcd_of_comparable` extend the pending proof by symmetry to all positive moduli comparable under divisibility. Nothing here settles moduli with neither dividing the other.

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
