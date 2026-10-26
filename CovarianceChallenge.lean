module

public import Mathlib

public section

/-!
# Independently auditable modular covariance statements

This file imports only Mathlib. It intentionally does not import
FourthMomentResearch or any other repository-specific module.
The identical definitions in CovarianceSolution are bridged to the
existing Lean proofs. The two theorem statements below are the
mathematical claims selected by comparator-covariance.json.
-/

namespace TruncatedSieveFluxComparator

/-- The mean of the fractional part of m/d for m in [0,H). -/
noncomputable def modularFractionMean (d H : ℕ) : ℝ :=
  (∑ n ∈ Finset.range H, (((n % d : ℕ) : ℝ) / (d : ℝ))) / (H : ℝ)

/-- The fractional part m/d with its H-sample mean subtracted. -/
noncomputable def centeredModularFraction (m d H : ℕ) : ℝ :=
  (((m % d : ℕ) : ℝ) / (d : ℝ)) - modularFractionMean d H

/-- The normalized, finite covariance of modular fractional parts. -/
noncomputable def empiricalModularCovariance (a b H : ℕ) : ℝ :=
  (∑ m ∈ Finset.range H,
    centeredModularFraction m a H * centeredModularFraction m b H) /
      (H : ℝ)

/-- The classical integer Möbius function, embedded into the reals. -/
noncomputable def moebiusReal (d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ)

/-- Signed truncated Möbius fractional-part sum. -/
noncomputable def roundingError (m B : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 B,
    moebiusReal d * (((m % d : ℕ) : ℝ) / (d : ℝ))

/-- Arithmetic mean of the truncated rounding error on [0,H). -/
noncomputable def empiricalErrorMean (B H : ℕ) : ℝ :=
  (∑ m ∈ Finset.range H, roundingError m B) / (H : ℝ)

/-- Centered second moment of the Möbius rounding error. -/
noncomputable def empiricalSecondMoment (B H : ℕ) : ℝ :=
  (∑ m ∈ Finset.range H,
    (roundingError m B - empiricalErrorMean B H) ^ 2) / (H : ℝ)

/-- Centered fourth moment of the signed Möbius rounding error. -/
noncomputable def empiricalFourthMoment (B H : ℕ) : ℝ :=
  (∑ m ∈ Finset.range H,
    (roundingError m B - empiricalErrorMean B H) ^ 4) / (H : ℝ)

/-- Full gcd covariance identity for arbitrary positive moduli
and every positive common averaging period. -/
theorem gcd_covariance
    (a b T : ℕ) (ha : 0 < a) (hb : 0 < b) (hTpos : 0 < T)
    (haT : a ∣ T) (hbT : b ∣ T) :
    empiricalModularCovariance a b T =
      (((Nat.gcd a b : ℝ) ^ 2 - 1) /
        (12 * (a : ℝ) * (b : ℝ))) := by
  sorry

/-- Exact finite gcd-weighted quadratic expression of the
centered second moment, without any assumed asymptotic bound. -/
theorem second_moment_gcd
    (B T : ℕ) (hTpos : 0 < T)
    (hT : ∀ d ∈ Finset.Icc 1 B, d ∣ T) :
    empiricalSecondMoment B T =
      ∑ a ∈ Finset.Icc 1 B,
      ∑ b ∈ Finset.Icc 1 B,
        (moebiusReal a * moebiusReal b) *
          (((Nat.gcd a b : ℝ) ^ 2 - 1) /
            (12 * (a : ℝ) * (b : ℝ))) := by
  sorry


/-- Unconditional elementary fourth-moment bound on common periods. -/
theorem fourth_moment_quartic
    (B T : ℕ) (hTpos : 0 < T)
    (hT : ∀ d ∈ Finset.Icc 1 B, d ∣ T) :
    empiricalFourthMoment B T ≤ ((B : ℝ) / 2) ^ 4 := by
  sorry

/-- Fourth moment controlled by B²/4 times the variance, on a
positive common period. -/
theorem fourth_moment_le_variance
    (B T : ℕ) (hTpos : 0 < T)
    (hT : ∀ d ∈ Finset.Icc 1 B, d ∣ T) :
    empiricalFourthMoment B T ≤
      ((B : ℝ) / 2) ^ 2 * empiricalSecondMoment B T := by
  sorry

/-- Conditional cubic estimate: the linear variance hypothesis is
a premise, not a theorem. This must not be advertised as an
unconditional O(B³) fourth-moment bound. -/
theorem fourth_moment_cubic_conditional
    (B T : ℕ) (C : ℝ) (hTpos : 0 < T)
    (hT : ∀ d ∈ Finset.Icc 1 B, d ∣ T)
    (hVariance : empiricalSecondMoment B T ≤ C * (B : ℝ)) :
    empiricalFourthMoment B T ≤ (C / 4) * (B : ℝ) ^ 3 := by
  sorry

end TruncatedSieveFluxComparator
