module

public import Solution

public section

namespace TruncatedSieveFlux

/-!
# Research scaffold: fourth moment of Möbius rounding errors

The genuine research target is a uniform bound of the form
  centeredFourthMoment B (Nat.lcm ... ) ≤ C * (B : ℝ)^2
with a constant C independent of B, over a full common period.

**That target is NOT proved here.**

This module establishes the much weaker, elementary O(B^4) estimate
on arbitrary finite averaging intervals. It checks the definitions,
the existing rounding-error bridge, and the basic normalization.

The three verified results in Solution.lean remain unmodified.
-/

/-- The finite rounding error, equal to the Möbius fractional-part sum. -/
noncomputable def roundingError (M B : ℕ) : ℝ :=
  (M : ℝ) * harmonicMoebiusMass B - floorWeightedMoebiusMass M B

/-- Exact expression as a Möbius-weighted sum of rational fractional parts.
For positive d, (M % d) / d is exactly the fractional part of M / d. -/
theorem roundingError_eq_mod_sum (M B : ℕ) :
    roundingError M B =
      ∑ d ∈ Finset.Icc 1 B,
        moebiusReal d * (((M % d : ℕ) : ℝ) / (d : ℝ)) := by
  unfold roundingError
  exact harmonic_floor_discrepancy_eq_mod_sum M B

/-- The normalized mean over a finite interval starting at zero. -/
noncomputable def empiricalErrorMean (B H : ℕ) : ℝ :=
  (∑ m ∈ Finset.range H, roundingError m B) / (H : ℝ)

/-- The corresponding centered fourth empirical moment. -/
noncomputable def empiricalFourthMoment (B H : ℕ) : ℝ :=
  (∑ m ∈ Finset.range H,
    (roundingError m B - empiricalErrorMean B H) ^ 4) / (H : ℝ)

/-- Reuse of the already verified quantitative rounding bound. -/
theorem abs_roundingError_le (M B : ℕ) :
    |roundingError M B| ≤ (B : ℝ) := by
  unfold roundingError
  simpa only [abs_sub_comm] using
    (moebius_floor_rounding_error_le M B)

/-- Bounding the empirical mean by the uniform pointwise bound. -/
theorem abs_empiricalErrorMean_le (B H : ℕ) (hH : 0 < H) :
    |empiricalErrorMean B H| ≤ (B : ℝ) := by
  have hpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  unfold empiricalErrorMean
  rw [abs_div, abs_of_nonneg (le_of_lt hpos)]
  apply (div_le_iff₀ hpos).2
  calc
    |∑ m ∈ Finset.range H, roundingError m B| ≤
      ∑ m ∈ Finset.range H, |roundingError m B| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.range H, (B : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      exact abs_roundingError_le m B
    _ = (B : ℝ) * (H : ℝ) := by simp [mul_comm]

/-- Elementary fallback, valid for every nonempty averaging interval.
It is O(B^4), not the conjectural O(B^2) bound. -/
theorem empiricalFourthMoment_le_trivial (B H : ℕ) (hH : 0 < H) :
    empiricalFourthMoment B H ≤ (2 * (B : ℝ)) ^ 4 := by
  have hpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hpoint (m : ℕ) :
      (roundingError m B - empiricalErrorMean B H)^4 ≤
        (2 * (B : ℝ))^4 := by
    have htri :
        |roundingError m B - empiricalErrorMean B H| ≤
          |roundingError m B| + |empiricalErrorMean B H| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        (abs_add_le (roundingError m B) (-empiricalErrorMean B H))
    have hb :
        |roundingError m B - empiricalErrorMean B H| ≤
          2 * (B : ℝ) := by
      calc
        _ ≤ |roundingError m B| + |empiricalErrorMean B H| := htri
        _ ≤ (B : ℝ) + (B : ℝ) :=
          add_le_add (abs_roundingError_le m B)
            (abs_empiricalErrorMean_le B H hH)
        _ = 2 * (B : ℝ) := by ring
    calc
      (roundingError m B - empiricalErrorMean B H)^4 =
          |roundingError m B - empiricalErrorMean B H|^4 := by
            rcases le_total 0 (roundingError m B - empiricalErrorMean B H) with ht | ht
            · rw [abs_of_nonneg ht]
            · rw [abs_of_nonpos ht]
              ring
      _ ≤ (2 * (B : ℝ))^4 := by
        gcongr
  unfold empiricalFourthMoment
  apply (div_le_iff₀ hpos).2
  calc
    (∑ m ∈ Finset.range H,
      (roundingError m B - empiricalErrorMean B H)^4) ≤
      ∑ m ∈ Finset.range H, (2 * (B : ℝ))^4 := by
        apply Finset.sum_le_sum
        intro m hm
        exact hpoint m
    _ = (2 * (B : ℝ))^4 * (H : ℝ) := by simp [mul_comm]

end TruncatedSieveFlux
