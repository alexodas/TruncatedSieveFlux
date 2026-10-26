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

For the diagonal over a full modulus, the proved identity is

```text
(1/d) * sum_{0 ≤ M < d} ((M mod d)/d - (d-1)/(2*d))^2
   = (d^2-1)/(12*d^2)   for d>0.
```

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
