# Research note: centered fourth moment of the Möbius rounding error

**Status: conjectural; the O(B^2) claim is NOT proved in Lean or mathematically established here.**
This is an exploratory research module; it does not assert a new proved fourth-moment theorem.

## Objective

For an integer cutoff B ≥ 2, let

- `L_B = lcm(1, ..., B)` (a common period);
- `E_B(M) = sum_{1 ≤ d ≤ B} mu(d) * ((M mod d) / d)`, for M ≥ 0;
- `mean_B = (1/L_B) * sum_{0 ≤ M < L_B} E_B(M)`.

The intended research theorem is that an **absolute** constant `C4 > 0`
exists such that, for all B ≥ 2,

```text
(1/L_B) * sum_{0 ≤ M < L_B} (E_B(M) - mean_B)^4 ≤ C4 * B^2.
```

The existence of such a constant, and the implications for positive-density
oscillations, require new work. No claim of mathematical originality is made.

## What has been proved in Lean

`FourthMomentResearch.lean`, built on `Solution.lean`, proves:

1. `abs_roundingError_le`: `|E_B(M)| ≤ B` using the
   logarithmic-cutoff rounding-error lemma.
2. `roundingError_eq_mod_sum`: the exact representation of `E_B(M)` as a
   finite weighted sum of rational fractional parts.
3. `abs_empiricalErrorMean_le`: the absolute empirical mean is at most B
   over any nonempty finite interval `[0,H)`.
4. `empiricalFourthMoment_le_trivial`: the centered empirical fourth
   moment over any nonempty finite interval is at most `(2B)^4`.

The fourth point is **O(B^4)**, not the sought **O(B^2)**. It does not imply
positive-density oscillations. Its main purpose is to check a complete
proof skeleton, notation and finite-sum normalization with the actual Lean
kernel while developing the substantially harder correlations.

## Main mathematical obstacle

Expanding the fourth power produces correlations between four functions
`(M mod d)/d`. Proving enough cancellation uniformly in B (and estimating
averages uniformly when the cutoff changes) is the central unresolved step.
Sampled values of the normalized fourth moment are only experimental
evidence; they cannot substitute for this estimate.

## Relation to the Möbius residual

The logarithmic-cutoff residual approximation in `Solution.lean` connects
the finite rounding error with the omitted Möbius mass. The research
module reuses its auxiliary finite-sum identities.

## Literature to compare

- Granville, Koukoulopoulos, Maynard, *Sieve weights and their smoothings*
  (Annales scientifiques de l'École normale supérieure, 2021),
  https://arxiv.org/abs/1606.06781 .
  Their work studies high moments of related truncated Möbius divisor sums;
  an originality claim for this proposed fourth moment would require a
  careful comparison, not just a keyword search.
