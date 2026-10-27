module

public import Mathlib
import all Solution
import all FourthMomentResearch

public section

/-!
# Independently auditable modular covariance statements

This Solution repeats the Challenge definitions verbatim and proves
all five selected statements by referencing the verified research
module. Comparator checks their agreement with independently
specified statements in the Mathlib-only CovarianceChallenge and
replays the proof dependencies through independent kernels.
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

/-- Full gcd covariance identity for arbitrary positive moduli
and every positive common averaging period. -/
theorem gcd_covariance
    (a b T : ℕ) (ha : 0 < a) (hb : 0 < b) (hTpos : 0 < T)
    (haT : a ∣ T) (hbT : b ∣ T) :
    empiricalModularCovariance a b T =
      (((Nat.gcd a b : ℝ) ^ 2 - 1) /
        (12 * (a : ℝ) * (b : ℝ))) := by
  exact TruncatedSieveFlux.empiricalModularCovariance_gcd_general
    a b T ha hb hTpos haT hbT

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
  have herror (m B : ℕ) :
      roundingError m B = TruncatedSieveFlux.roundingError m B :=
    (TruncatedSieveFlux.roundingError_eq_mod_sum m B).symm
  have hmean :
      empiricalErrorMean B T =
        TruncatedSieveFlux.empiricalErrorMean B T := by
    unfold empiricalErrorMean TruncatedSieveFlux.empiricalErrorMean
    apply congrArg (fun y : ℝ => y / (T : ℝ))
    apply Finset.sum_congr rfl
    intro m hm
    exact herror m B
  have hvariance :
      empiricalSecondMoment B T =
        TruncatedSieveFlux.empiricalSecondMoment B T := by
    unfold empiricalSecondMoment TruncatedSieveFlux.empiricalSecondMoment
    rw [hmean]
    apply congrArg (fun y : ℝ => y / (T : ℝ))
    apply Finset.sum_congr rfl
    intro m hm
    rw [herror m B]
  rw [hvariance]
  exact TruncatedSieveFlux.empiricalSecondMoment_eq_gcd_sum
    B T hTpos hT


/-- Centered fourth moment of the signed Möbius rounding error. -/
noncomputable def empiricalFourthMoment (B H : ℕ) : ℝ :=
  (∑ m ∈ Finset.range H,
    (roundingError m B - empiricalErrorMean B H) ^ 4) / (H : ℝ)

private theorem bridge_error (m B : ℕ) :
    roundingError m B = TruncatedSieveFlux.roundingError m B :=
  (TruncatedSieveFlux.roundingError_eq_mod_sum m B).symm

private theorem bridge_mean (B H : ℕ) :
    empiricalErrorMean B H =
      TruncatedSieveFlux.empiricalErrorMean B H := by
  unfold empiricalErrorMean TruncatedSieveFlux.empiricalErrorMean
  apply congrArg (fun y : ℝ => y / (H : ℝ))
  apply Finset.sum_congr rfl
  intro m hm
  exact bridge_error m B

private theorem bridge_second (B H : ℕ) :
    empiricalSecondMoment B H =
      TruncatedSieveFlux.empiricalSecondMoment B H := by
  unfold empiricalSecondMoment TruncatedSieveFlux.empiricalSecondMoment
  rw [bridge_mean B H]
  apply congrArg (fun y : ℝ => y / (H : ℝ))
  apply Finset.sum_congr rfl
  intro m hm
  rw [bridge_error m B]

private theorem bridge_fourth (B H : ℕ) :
    empiricalFourthMoment B H =
      TruncatedSieveFlux.empiricalFourthMoment B H := by
  unfold empiricalFourthMoment TruncatedSieveFlux.empiricalFourthMoment
  rw [bridge_mean B H]
  apply congrArg (fun y : ℝ => y / (H : ℝ))
  apply Finset.sum_congr rfl
  intro m hm
  rw [bridge_error m B]

/-- Unconditional elementary fourth-moment bound on common periods. -/
theorem fourth_moment_quartic
    (B T : ℕ) (hTpos : 0 < T)
    (hT : ∀ d ∈ Finset.Icc 1 B, d ∣ T) :
    empiricalFourthMoment B T ≤ ((B : ℝ) / 2) ^ 4 := by
  rw [bridge_fourth]
  exact TruncatedSieveFlux.empiricalFourthMoment_le_half_quartic
    B T hTpos hT

/-- Fourth moment controlled by B²/4 times the variance. -/
theorem fourth_moment_le_variance
    (B T : ℕ) (hTpos : 0 < T)
    (hT : ∀ d ∈ Finset.Icc 1 B, d ∣ T) :
    empiricalFourthMoment B T ≤
      ((B : ℝ) / 2) ^ 2 * empiricalSecondMoment B T := by
  rw [bridge_fourth, bridge_second]
  exact TruncatedSieveFlux.empiricalFourthMoment_le_secondMoment_mul
    B T hTpos hT

/-- Conditional cubic estimate; the linear variance bound is a premise. -/
theorem fourth_moment_cubic_conditional
    (B T : ℕ) (C : ℝ) (hTpos : 0 < T)
    (hT : ∀ d ∈ Finset.Icc 1 B, d ∣ T)
    (hVariance : empiricalSecondMoment B T ≤ C * (B : ℝ)) :
    empiricalFourthMoment B T ≤ (C / 4) * (B : ℝ) ^ 3 := by
  have hvar := hVariance
  rw [bridge_second] at hvar
  rw [bridge_fourth]
  exact TruncatedSieveFlux.empiricalFourthMoment_le_cubic_of_variance_le
    B T C hTpos hT hvar

end TruncatedSieveFluxComparator
