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

**Full gcd covariance formalized.** After proving the boundary
cases, diagonal identities, period invariance, and coprime CRT
factorization, the new theorem
`empiricalModularCovariance_gcd_general` proves for all positive
`a,b,T` with `a ∣ T` and `b ∣ T`:

```text
C_(a,b;T) = (gcd(a,b)^2-1)/(12*a*b).
```

The proof is fully general, including cases in which
`gcd(a,b)>1` and neither modulus divides the other.
Its GitHub Actions Lean `verify` job passed on commit
`0bfbf58`. The theorem
`empiricalSecondMoment_eq_gcd_sum` then gives the exact
finite identity

```text
V_(B,T) = sum_{1 ≤ a,b ≤ B} mu(a)*mu(b)*
          (gcd(a,b)^2 - 1)/(12*a*b).
```

This establishes a complete **finite arithmetic expression**
for the second moment, not a new unconditional bound on it.

For the diagonal over a full modulus, the proved identity is

```text
(1/d) * sum_{0 ≤ M < d} ((M mod d)/d - (d-1)/(2*d))^2
   = (d^2-1)/(12*d^2)   for d>0.
```

**Full-period moment invariance (new formalization).** The new Lean theorems `empiricalSecondMoment_eq_of_common_periods` and `empiricalFourthMoment_eq_of_common_periods` respectively identify the entire variance and the entire centered fourth moment on any two positive periods divisible by every `1 ≤ d ≤ B`. The second-moment theorem combines the Möbius quadratic-form identity with `empiricalModularCovariance_eq_lcm`; the fourth-moment theorem sums the periodic centered fourth power over repeated cycles and compares periods through their least common multiple. Both moment-invariance proof scripts have passed the GitHub Actions Lean `verify` compilation; their distinct theorem statements are not individually listed as Comparator targets. The Comparator checks the main finite sieve theorem and the two separately stated covariance/variance research claims. Their conclusions are exact period-independence identities, **not** the conjectured `O(B²)` bound.

**Four-divisor correlations.**
`empiricalFourthMoment_eq_fourfold_sum` expands the full empirical
fourth moment into products of four centered modular fractions.
These expansions are exact, but do not establish cancellation.

## Supporting formalization

The `Solution.lean` module supplies the finite Möbius divisor-sieve
identity and the quotient/remainder bound. The original `comparator.json` selects only
`moebius_log_cutoff_residual_approximation`, which bounds
the residual-rounding discrepancy by the integer cutoff.
The second `comparator-covariance.json` selects five
Mathlib-only challenge statements: the general gcd covariance,
exact second moment, unconditional quartic fourth-moment bound,
fourth-to-second-moment inequality, and the conditional cubic
estimate. The first two wrappers passed NanoDa and con-ron;
the three further fourth-moment comparisons have been added
and await their own Comparator CI result. Other helper
theorems are not individually selected. Auxiliary
lemmas prove the modular mean over any number of full periods,
the rational remainder representation, and the unconditional
`16 B^4` centered fourth-moment bound on nonempty averaging
intervals. On positive common periods Lean gives the sharper
`B^4/16` estimate. Neither is a quadratic bound.

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

A **partially machine-checked derivation** uses the classical
finite-period covariance formula (now proved in Lean)

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

**Verification status:** the full gcd covariance identity and
the exact gcd-weighted second-moment formula are proved in Lean.
The arithmetic upper bound `V_B ≤ 3B/4` and the resulting
unconditional cubic fourth-moment estimate are **not yet
proved in Lean**.
The covariance identity is classical; see for example
https://math.stackexchange.com/questions/140499/a-sum-of-fractional-parts .
The paper-level estimate should be independently reviewed.
No claim of originality is made.

### Complete gcd-fiber argument (Lean verified)

For arbitrary `a,b>0`, put `g=gcd(a,b)`, `r=a/g`
and `s=b/g`. The reduced moduli `r,s` are coprime.
First calculate on the positive common period
`P=g*r*s` by writing `m=k*g+t`, where
`0≤t<g` and `0≤k<r*s`. Period-invariance then
extends the result to every other positive common period `T`.
The new lemmas
`sum_range_mul_blocks`, `gcd_fiber_mod` and
`centered_residue_on_gcd_fiber` provide the exact
identity

```text
centered_(g*r)(k*g+t) =
  centered_r(k) + (t-(g-1)/2)/(g*r).
```

For the second modulus, replace `r` by `s`.
The CRT product factorization annihilates the mixed
terms, leaving the squared correction from the common
remainder `t`. The lemma
`coprime_centered_shifted_product_sum` formalizes this
step for all positive coprime quotients simultaneously.
Summing over `t` is exactly the previously verified
diagonal covariance computation at modulus `g`.
The assembly theorem `empiricalModularCovariance_mul_coprime`
and the final `empiricalModularCovariance_gcd_general`
have passed the Lean build. The latter has now additionally
been re-stated in a Mathlib-only `CovarianceChallenge` and
compared against `CovarianceSolution` through
`comparator-covariance.json`, alongside the exact finite
second moment. The separate Comparator run for those two research statements
passed both NanoDa and con-ron. Three additional fourth-moment
statements have been added to the same comparison; their
new independent-kernel outcome is still pending.
Individual auxiliary lemmas are not separately named
Comparator declarations.
The theorem `empiricalModularCovariance_gcd_general` has
**no additional coprimality, divisibility between the two moduli,
or particular-modulus assumptions**: it requires only positive
moduli and a positive averaging period divisible by both.

The exact variance corollary
`empiricalSecondMoment_eq_gcd_sum` eliminates all
unevaluated pairwise covariances. It remains to formalize
a **quantitative bound** on this finite gcd sum, then
study cancellation in the fourth-order correlations.
Neither the desired `O(B²)` fourth-moment bound nor
its proposed oscillation consequences follow automatically.

## What must be proved next

The pairwise covariance formula is now complete. The next
arithmetical verification goal is the paper-derived bound

```text
sum_{1 ≤ a,b ≤ B} gcd(a,b)^2/(a*b) ≤ 9B,
V_(B,T) ≤ 3B/4,
fourth_(B,T) ≤ 3B³/16,
```

for positive common periods, followed by a genuinely
stronger analysis of the four-divisor correlations if one
wants an `O(B²)` centered fourth moment. The last bound
remains the principal open research question and cannot
be inferred from a complete second-moment calculation.

## Literature and originality

Closely related high moments and truncations occur in Granville,
Koukoulopoulos and Maynard, *Sieve weights and their smoothings*
(2016 preprint; later publication):
https://arxiv.org/abs/1606.06781.
Existing fractional-part and gcd-covariance identities also overlap
with this area. Novelty requires a substantive mathematical and
bibliographic review rather than a successful Lean compilation.
