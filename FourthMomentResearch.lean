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

The logarithmic-cutoff residual theorem in Solution.lean provides the
finite rounding-error estimate used below.
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


/-! ## Exact arithmetic periodicity of the rounding error -/

/-- A common multiple of all positive d ≤ B is a period of the
Möbius-weighted rounding discrepancy. -/
theorem roundingError_add_common_period
    (M B T : ℕ)
    (hT : ∀ d ∈ Finset.Icc 1 B, d ∣ T) :
    roundingError (M + T) B = roundingError M B := by
  rw [roundingError_eq_mod_sum, roundingError_eq_mod_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hmod : T % d = 0 := Nat.mod_eq_zero_of_dvd (hT d hd)
  have hadd : (M + T) % d = M % d := by
    simp [Nat.add_mod, hmod]
  rw [hadd]

/-- In particular, B! is a valid period for every integer cutoff B. -/
theorem roundingError_add_factorial (M B : ℕ) :
    roundingError (M + B.factorial) B = roundingError M B := by
  apply roundingError_add_common_period
  intro d hd
  exact Nat.dvd_factorial (Finset.mem_Icc.mp hd).1
    (Finset.mem_Icc.mp hd).2

/-- The normalized mean over a finite interval starting at zero. -/
noncomputable def empiricalErrorMean (B H : ℕ) : ℝ :=
  (∑ m ∈ Finset.range H, roundingError m B) / (H : ℝ)

/-- The corresponding centered fourth empirical moment. -/
noncomputable def empiricalFourthMoment (B H : ℕ) : ℝ :=
  (∑ m ∈ Finset.range H,
    (roundingError m B - empiricalErrorMean B H) ^ 4) / (H : ℝ)


/-! ## Centering as a sum of centered modular fractions -/

/-- The empirical mean of a single rational fractional-part summand. -/
noncomputable def modularFractionMean (d H : ℕ) : ℝ :=
  (∑ n ∈ Finset.range H, (((n % d : ℕ) : ℝ) / (d : ℝ))) / (H : ℝ)

/-- The exact average of a rational fractional part over one complete
modulus: 0, 1/d, ..., (d-1)/d. -/
theorem modularFractionMean_self (d : ℕ) (hd : 0 < d) :
    modularFractionMean d d =
      (((d - 1 : ℕ) : ℝ) / (2 * (d : ℝ))) := by
  have hne : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hsum :
      (∑ n ∈ Finset.range d, (n : ℝ)) * 2 =
        (d : ℝ) * (((d - 1 : ℕ) : ℝ)) := by
    have hnat := congrArg (fun z : ℕ => (z : ℝ))
      (Finset.sum_range_id_mul_two d)
    simpa using hnat
  have hmod :
      (∑ n ∈ Finset.range d, (((n % d : ℕ) : ℝ) / (d : ℝ))) =
        ∑ n ∈ Finset.range d, ((n : ℝ) / (d : ℝ)) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hn)]
  unfold modularFractionMean
  rw [hmod, ← Finset.sum_div]
  have hsum' := congrArg (fun z : ℝ => z * (d : ℝ)) hsum
  calc
    ((∑ n ∈ Finset.range d, (n : ℝ)) / (d : ℝ)) / (d : ℝ) =
        (∑ n ∈ Finset.range d, (n : ℝ)) / ((d : ℝ) * (d : ℝ)) := by
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
    _ = (((d - 1 : ℕ) : ℝ) / (2 * (d : ℝ))) := by
          apply (div_eq_div_iff (mul_ne_zero hne hne)
            (mul_ne_zero (by norm_num) hne)).2
          nlinarith [hsum']

/-- Summing the fractional parts over q complete cycles gives q copies
of the sum over the basic modulus. -/
private theorem modularFraction_sum_mul (d q : ℕ) :
    (∑ n ∈ Finset.range (q * d), (((n % d : ℕ) : ℝ) / (d : ℝ))) =
      (q : ℝ) * ∑ n ∈ Finset.range d, (((n % d : ℕ) : ℝ) / (d : ℝ)) := by
  let f : ℕ → ℝ := fun n => (((n % d : ℕ) : ℝ) / (d : ℝ))
  change (∑ n ∈ Finset.range (q * d), f n) =
    (q : ℝ) * ∑ n ∈ Finset.range d, f n
  induction q with
  | zero => simp
  | succ q ih =>
      calc
        (∑ n ∈ Finset.range (q.succ * d), f n) =
            (∑ n ∈ Finset.range (q * d), f n) +
            (∑ n ∈ Finset.range d, f (q * d + n)) := by
              simpa only [Nat.succ_mul] using
                (Finset.sum_range_add f (q * d) d)
        _ = (∑ n ∈ Finset.range (q * d), f n) +
            (∑ n ∈ Finset.range d, f n) := by
              congr 1
              apply Finset.sum_congr rfl
              intro n hn
              simp [f, Nat.add_mod, Nat.mul_mod]
        _ = (q.succ : ℝ) * ∑ n ∈ Finset.range d, f n := by
              rw [ih]
              push_cast
              ring

/-- Every positive integer multiple of d has the same average fractional
part as one basic d-period. -/
theorem modularFractionMean_multiple (d q : ℕ) (hd : 0 < d) (hq : 0 < q) :
    modularFractionMean d (q * d) =
      (((d - 1 : ℕ) : ℝ) / (2 * (d : ℝ))) := by
  have hqne : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hbase := modularFractionMean_self d hd
  unfold modularFractionMean at hbase ⊢
  rw [modularFraction_sum_mul d q, Nat.cast_mul]
  calc
    ((q : ℝ) *
      (∑ n ∈ Finset.range d, (((n % d : ℕ) : ℝ) / (d : ℝ)))) /
        ((q : ℝ) * (d : ℝ)) =
      (∑ n ∈ Finset.range d, (((n % d : ℕ) : ℝ) / (d : ℝ))) / (d : ℝ) := by
        field_simp [hqne, hdne]
    _ = (((d - 1 : ℕ) : ℝ) / (2 * (d : ℝ))) := hbase

/-- Exact regrouping: averaging the Möbius sum amounts to summing the
averages of its individual rational fractional-part terms. -/
theorem empiricalErrorMean_eq_weighted_modular_means (B H : ℕ) :
    empiricalErrorMean B H =
      ∑ d ∈ Finset.Icc 1 B, moebiusReal d * modularFractionMean d H := by
  classical
  unfold empiricalErrorMean modularFractionMean
  simp_rw [roundingError_eq_mod_sum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- Exact Möbius rounding-error mean on any positive common period.
The mean is independent of which common multiple is chosen. -/
theorem empiricalErrorMean_common_period
    (B T : ℕ) (hTpos : 0 < T)
    (hT : ∀ d ∈ Finset.Icc 1 B, d ∣ T) :
    empiricalErrorMean B T =
      ∑ d ∈ Finset.Icc 1 B,
        moebiusReal d * (((d - 1 : ℕ) : ℝ) / (2 * (d : ℝ))) := by
  rw [empiricalErrorMean_eq_weighted_modular_means]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨q, hq⟩ := hT d hd
  have hqpos : 0 < q := by
    by_contra hn
    have hqzero : q = 0 := by omega
    have hTzero : T = 0 := by simpa [hqzero] using hq
    omega
  rw [hq, Nat.mul_comm d q, modularFractionMean_multiple d q
    (Finset.mem_Icc.mp hd).1 hqpos]

/-- B! is a concrete common period, so its mean has a fully explicit
expression in the Möbius coefficients and the divisor indices. -/
theorem empiricalErrorMean_factorial (B : ℕ) :
    empiricalErrorMean B B.factorial =
      ∑ d ∈ Finset.Icc 1 B,
        moebiusReal d * (((d - 1 : ℕ) : ℝ) / (2 * (d : ℝ))) := by
  apply empiricalErrorMean_common_period B B.factorial (Nat.factorial_pos B)
  intro d hd
  exact Nat.dvd_factorial (Finset.mem_Icc.mp hd).1
    (Finset.mem_Icc.mp hd).2

/-- Exact centering formula for the Möbius error on every positive
common period. The subtracted mean is independent of the chosen period. -/
theorem centered_roundingError_common_period (M B T : ℕ)
    (hTpos : 0 < T) (hT : ∀ d ∈ Finset.Icc 1 B, d ∣ T) :
    roundingError M B - empiricalErrorMean B T =
      ∑ d ∈ Finset.Icc 1 B,
        moebiusReal d *
          ((((M % d : ℕ) : ℝ) / (d : ℝ)) -
            (((d - 1 : ℕ) : ℝ) / (2 * (d : ℝ)))) := by
  rw [roundingError_eq_mod_sum,
    empiricalErrorMean_common_period B T hTpos hT,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- Each centered error is a weighted sum of centered modular fractions.
This is the direct starting point for a fourth-order correlation expansion. -/
theorem centered_roundingError_eq_modular_sum (M B H : ℕ) :
    roundingError M B - empiricalErrorMean B H =
      ∑ d ∈ Finset.Icc 1 B,
        moebiusReal d *
          ((((M % d : ℕ) : ℝ) / (d : ℝ)) - modularFractionMean d H) := by
  rw [roundingError_eq_mod_sum, empiricalErrorMean_eq_weighted_modular_means]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring


/-! ## Fourth-order expansion of a finite weighted sum -/

/-- A purely algebraic expansion of a fourth power as an ordered
four-fold sum. It does not impose any cancellation. -/
private theorem fourth_power_finset_sum (s : Finset ℕ) (f : ℕ → ℝ) :
    (∑ d ∈ s, f d) ^ 4 =
      ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
        f a * f b * f c * f d := by
  simp only [pow_succ, pow_zero, mul_one,
    Finset.sum_mul, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]


/-- The local centered rational fractional part at a fixed divisor. -/
noncomputable def centeredModularFraction (M d H : ℕ) : ℝ :=
  (((M % d : ℕ) : ℝ) / (d : ℝ)) - modularFractionMean d H

/-- The exact fourth-moment tensor prior to any analytic cancellation:
this identity isolates the four-divisor correlations that would need
to be bounded to obtain O(B²) instead of the trivial O(B⁴). -/
theorem empiricalFourthMoment_eq_fourfold_sum (B H : ℕ) :
    empiricalFourthMoment B H =
      (∑ m ∈ Finset.range H,
        ∑ a ∈ Finset.Icc 1 B,
        ∑ b ∈ Finset.Icc 1 B,
        ∑ c ∈ Finset.Icc 1 B,
        ∑ d ∈ Finset.Icc 1 B,
          (moebiusReal a * centeredModularFraction m a H) *
          (moebiusReal b * centeredModularFraction m b H) *
          (moebiusReal c * centeredModularFraction m c H) *
          (moebiusReal d * centeredModularFraction m d H)) / (H : ℝ) := by
  unfold empiricalFourthMoment
  apply congrArg (fun y : ℝ => y / (H : ℝ))
  apply Finset.sum_congr rfl
  intro m hm
  rw [centered_roundingError_eq_modular_sum]
  change (∑ d ∈ Finset.Icc 1 B,
      moebiusReal d * centeredModularFraction m d H) ^ 4 = _
  exact fourth_power_finset_sum (Finset.Icc 1 B)
    (fun d => moebiusReal d * centeredModularFraction m d H)


/-! ## Second moment and two-divisor correlations -/

/-- The empirical centered second moment (variance) of the rounding error. -/
noncomputable def empiricalSecondMoment (B H : ℕ) : ℝ :=
  (∑ m ∈ Finset.range H,
    (roundingError m B - empiricalErrorMean B H) ^ 2) / (H : ℝ)

/-- Finite empirical covariance of the modular fractions for two moduli. -/
noncomputable def empiricalModularCovariance (a b H : ℕ) : ℝ :=
  (∑ m ∈ Finset.range H,
    centeredModularFraction m a H * centeredModularFraction m b H) / (H : ℝ)

/-- Exact pairwise expansion of the centered second moment. This exposes the
two-modulus correlations to be evaluated in the next arithmetic step. -/
theorem empiricalSecondMoment_eq_pairwise_sum (B H : ℕ) :
    empiricalSecondMoment B H =
      (∑ m ∈ Finset.range H,
        ∑ a ∈ Finset.Icc 1 B,
        ∑ b ∈ Finset.Icc 1 B,
          (moebiusReal a * centeredModularFraction m a H) *
          (moebiusReal b * centeredModularFraction m b H)) / (H : ℝ) := by
  unfold empiricalSecondMoment
  apply congrArg (fun y : ℝ => y / (H : ℝ))
  apply Finset.sum_congr rfl
  intro m hm
  rw [centered_roundingError_eq_modular_sum]
  change (∑ d ∈ Finset.Icc 1 B,
      moebiusReal d * centeredModularFraction m d H) ^ 2 = _
  simpa only [pow_two] using
    (Finset.sum_mul_sum (Finset.Icc 1 B) (Finset.Icc 1 B)
      (fun d => moebiusReal d * centeredModularFraction m d H)
      (fun d => moebiusReal d * centeredModularFraction m d H))


/-- Exact expression for the finite centered variance as a quadratic form
in the pairwise modular covariances. -/
theorem empiricalSecondMoment_eq_covariance_sum (B H : ℕ) :
    empiricalSecondMoment B H =
      ∑ a ∈ Finset.Icc 1 B,
      ∑ b ∈ Finset.Icc 1 B,
        (moebiusReal a * moebiusReal b) *
          empiricalModularCovariance a b H := by
  classical
  rw [empiricalSecondMoment_eq_pairwise_sum]
  calc
    (∑ m ∈ Finset.range H,
        ∑ a ∈ Finset.Icc 1 B,
        ∑ b ∈ Finset.Icc 1 B,
          (moebiusReal a * centeredModularFraction m a H) *
            (moebiusReal b * centeredModularFraction m b H)) / (H : ℝ) =
      (∑ a ∈ Finset.Icc 1 B,
        ∑ b ∈ Finset.Icc 1 B,
        ∑ m ∈ Finset.range H,
          (moebiusReal a * centeredModularFraction m a H) *
            (moebiusReal b * centeredModularFraction m b H)) / (H : ℝ) := by
        apply congrArg (fun z : ℝ => z / (H : ℝ))
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_comm]
    _ = ∑ a ∈ Finset.Icc 1 B,
        ∑ b ∈ Finset.Icc 1 B,
        (moebiusReal a * moebiusReal b) *
          empiricalModularCovariance a b H := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro b hb
        unfold empiricalModularCovariance
        calc
          (∑ m ∈ Finset.range H,
              (moebiusReal a * centeredModularFraction m a H) *
                (moebiusReal b * centeredModularFraction m b H)) / (H : ℝ) =
            ((moebiusReal a * moebiusReal b) *
              ∑ m ∈ Finset.range H,
                centeredModularFraction m a H *
                  centeredModularFraction m b H) / (H : ℝ) := by
                congr 1
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro m hm
                ring
          _ = (moebiusReal a * moebiusReal b) *
                ((∑ m ∈ Finset.range H,
                  centeredModularFraction m a H *
                    centeredModularFraction m b H) / (H : ℝ)) := by ring

/-- A centered second moment is nonnegative on every finite interval,
with no arithmetic hypotheses. -/
theorem empiricalSecondMoment_nonneg (B H : ℕ) :
    0 ≤ empiricalSecondMoment B H := by
  unfold empiricalSecondMoment
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro m hm
    positivity
  · positivity

/-- Empirical modular covariance is symmetric. -/
theorem empiricalModularCovariance_comm (a b H : ℕ) :
    empiricalModularCovariance a b H =
      empiricalModularCovariance b a H := by
  unfold empiricalModularCovariance
  apply congrArg (fun y : ℝ => y / (H : ℝ))
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- Real form of the classical finite sum of squares. -/
private theorem sum_range_square_real (d : ℕ) :
    (∑ m ∈ Finset.range d, (m : ℝ) ^ 2) * 6 =
      (d : ℝ) * ((d : ℝ) - 1) * (2 * (d : ℝ) - 1) := by
  induction d with
  | zero => norm_num
  | succ d ih =>
      simp only [Finset.sum_range_succ, Nat.cast_succ]
      nlinarith [ih]


/-- Diagonal modular covariance over one complete modulus.
This is the classical variance (d²-1)/(12d²) of the discrete uniform grid. -/
theorem empiricalModularCovariance_diagonal (d : ℕ) (hd : 0 < d) :
    empiricalModularCovariance d d d =
      (((d : ℝ) ^ 2 - 1) / (12 * (d : ℝ) ^ 2)) := by
  let D : ℝ := (d : ℝ)
  let C : ℝ := (((d - 1 : ℕ) : ℝ) / (2 * D))
  let S₁ : ℝ := ∑ m ∈ Finset.range d, (m : ℝ)
  let S₂ : ℝ := ∑ m ∈ Finset.range d, (m : ℝ) ^ 2
  have hD : D ≠ 0 := by
    dsimp [D]
    exact_mod_cast (Nat.ne_of_gt hd)
  have hsubNat : 1 ≤ d := hd
  have hsub : (((d - 1 : ℕ) : ℝ)) = D - 1 := by
    dsimp [D]
    rw [Nat.cast_sub hsubNat]
    norm_num
  have hS₁ : S₁ * 2 = D * (D - 1) := by
    dsimp [S₁, D]
    have hnat := congrArg (fun z : ℕ => (z : ℝ))
      (Finset.sum_range_id_mul_two d)
    simpa [hsub] using hnat
  have hS₂ : S₂ * 6 = D * (D - 1) * (2 * D - 1) := by
    exact sum_range_square_real d
  have hC : C = (D - 1) / (2 * D) := by
    dsimp [C]
    rw [hsub]
  have hcov :
      empiricalModularCovariance d d d =
        (∑ m ∈ Finset.range d, ((m : ℝ) / D - C) ^ 2) / D := by
    unfold empiricalModularCovariance
    apply congrArg (fun y : ℝ => y / (d : ℝ))
    apply Finset.sum_congr rfl
    intro m hm
    simp only [centeredModularFraction, modularFractionMean_self d hd,
      Nat.mod_eq_of_lt (Finset.mem_range.mp hm)]
    dsimp [D, C]
    ring
  have hsum :
      (∑ m ∈ Finset.range d, ((m : ℝ) / D - C) ^ 2) =
        S₂ / D ^ 2 - (2 * C / D) * S₁ + D * C ^ 2 := by
    have hterm (m : ℕ) :
        ((m : ℝ) / D - C) ^ 2 =
          (m : ℝ) ^ 2 / D ^ 2 - (2 * C / D) * (m : ℝ) + C ^ 2 := by ring
    calc
      (∑ m ∈ Finset.range d, ((m : ℝ) / D - C) ^ 2) =
          ∑ m ∈ Finset.range d,
            ((m : ℝ) ^ 2 / D ^ 2 - (2 * C / D) * (m : ℝ) + C ^ 2) := by
              apply Finset.sum_congr rfl
              intro m hm
              exact hterm m
      _ = S₂ / D ^ 2 - (2 * C / D) * S₁ + D * C ^ 2 := by
              dsimp [S₁, S₂, D]
              simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                div_eq_mul_inv, ← Finset.sum_mul, ← Finset.mul_sum,
                Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hcov, hsum, hC]
  dsimp [D]
  field_simp
  nlinarith [hS₁, hS₂,
    congrArg (fun x : ℝ => x * (D - 1)) hS₁]

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

/-! ## Quantitative fourth-moment reductions -/

/-- The centered rational fractional part is bounded by one half.
Unlike an empirical centering, the midpoint of a full modulus is explicit. -/
private theorem abs_centered_modular_fraction_le_half
    (M d : ℕ) (hd : 0 < d) :
    |((M % d : ℕ) : ℝ) / (d : ℝ) -
       (((d - 1 : ℕ) : ℝ) / (2 * (d : ℝ)))| ≤ (1 / 2 : ℝ) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hle : M % d ≤ d - 1 := by
    have hmod := Nat.mod_lt M hd
    omega
  have hleR : (((M % d : ℕ) : ℝ)) ≤ (((d - 1 : ℕ) : ℝ)) := by
    exact_mod_cast hle
  have htop : (((d - 1 : ℕ) : ℝ)) ≤ (d : ℝ) := by
    exact_mod_cast Nat.sub_le d 1
  have hfrac0 : (0 : ℝ) ≤ (((M % d : ℕ) : ℝ) / (d : ℝ)) := by
    positivity
  have hfrac_le :
      (((M % d : ℕ) : ℝ) / (d : ℝ)) ≤
        (((d - 1 : ℕ) : ℝ) / (d : ℝ)) := by
    apply (div_le_div_iff₀ hdR hdR).2
    nlinarith [hleR]
  have hcenter :
      (((d - 1 : ℕ) : ℝ) / (2 * (d : ℝ))) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (d : ℝ))).2
    nlinarith [htop]
  have hdouble :
      (((d - 1 : ℕ) : ℝ) / (d : ℝ)) =
        2 * (((d - 1 : ℕ) : ℝ) / (2 * (d : ℝ))) := by
    field_simp [ne_of_gt hdR] <;> ring
  apply abs_le.mpr
  constructor <;> linarith

/-- Sharp uniform half-size upper bound for the centered rounding error
on every positive common period. -/
theorem abs_centered_roundingError_common_period_le_half
    (M B T : ℕ) (hTpos : 0 < T)
    (hT : ∀ d ∈ Finset.Icc 1 B, d ∣ T) :
    |roundingError M B - empiricalErrorMean B T| ≤ (B : ℝ) / 2 := by
  rw [centered_roundingError_common_period M B T hTpos hT]
  calc
    |∑ d ∈ Finset.Icc 1 B,
      moebiusReal d *
        (((M % d : ℕ) : ℝ) / (d : ℝ) -
          (((d - 1 : ℕ) : ℝ) / (2 * (d : ℝ))))| ≤
        ∑ d ∈ Finset.Icc 1 B,
          |moebiusReal d *
            (((M % d : ℕ) : ℝ) / (d : ℝ) -
              (((d - 1 : ℕ) : ℝ) / (2 * (d : ℝ))))| :=
                Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 B, (1 / 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      calc
        |moebiusReal d| *
          |((M % d : ℕ) : ℝ) / (d : ℝ) -
            (((d - 1 : ℕ) : ℝ) / (2 * (d : ℝ)))| ≤
          1 * (1 / 2 : ℝ) := by
            apply mul_le_mul (moebiusReal_abs_le_one d)
              (abs_centered_modular_fraction_le_half M d
                (Finset.mem_Icc.mp hd).1)
              (abs_nonneg _) (by norm_num)
        _ = (1 / 2 : ℝ) := by ring
    _ = (B : ℝ) / 2 := by
      simp [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] <;> ring

/-- A fourth moment on any complete common period is dominated by its
variance times B²/4. This reduces the power-four problem to a
second-moment estimate, but it is not by itself an O(B³) theorem. -/
theorem empiricalFourthMoment_le_secondMoment_mul
    (B T : ℕ) (hTpos : 0 < T)
    (hT : ∀ d ∈ Finset.Icc 1 B, d ∣ T) :
    empiricalFourthMoment B T ≤
      ((B : ℝ) / 2) ^ 2 * empiricalSecondMoment B T := by
  have hTreal : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hTpos
  have hpoint (m : ℕ) :
      (roundingError m B - empiricalErrorMean B T)^4 ≤
        ((B : ℝ) / 2)^2 *
          (roundingError m B - empiricalErrorMean B T)^2 := by
    let z := roundingError m B - empiricalErrorMean B T
    have hz : |z| ≤ (B : ℝ) / 2 :=
      abs_centered_roundingError_common_period_le_half m B T hTpos hT
    have hsq : z^2 ≤ ((B : ℝ) / 2)^2 := by
      have hsqabs : z^2 = |z|^2 := by
        rcases le_total 0 z with hp | hp
        · rw [abs_of_nonneg hp]
        · rw [abs_of_nonpos hp]
          ring
      calc
        z^2 = |z|^2 := hsqabs
        _ ≤ ((B : ℝ) / 2)^2 := by gcongr
    change z ^ 4 ≤ ((B : ℝ) / 2)^2 * z^2
    calc
      z^4 = z^2 * z^2 := by ring
      _ ≤ ((B : ℝ) / 2)^2 * z^2 :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg z)
  unfold empiricalFourthMoment empiricalSecondMoment
  calc
    (∑ m ∈ Finset.range T,
      (roundingError m B - empiricalErrorMean B T)^4) / (T : ℝ) ≤
        (∑ m ∈ Finset.range T,
          ((B : ℝ) / 2)^2 *
            (roundingError m B - empiricalErrorMean B T)^2) / (T : ℝ) := by
          apply div_le_div_of_nonneg_right
            (Finset.sum_le_sum (fun m hm => hpoint m))
            (le_of_lt hTreal)
    _ = ((B : ℝ) / 2)^2 *
          ((∑ m ∈ Finset.range T,
            (roundingError m B - empiricalErrorMean B T)^2) / (T : ℝ)) := by
          rw [← Finset.mul_sum]
          ring

/-- An unconditional improvement of the previous *constant* 16B⁴:
over a complete common period the centered fourth moment is at most
B⁴/16. Its exponent is still 4, not the conjectural exponent 2. -/
theorem empiricalFourthMoment_le_half_quartic
    (B T : ℕ) (hTpos : 0 < T)
    (hT : ∀ d ∈ Finset.Icc 1 B, d ∣ T) :
    empiricalFourthMoment B T ≤ ((B : ℝ) / 2)^4 := by
  have hTreal : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hTpos
  have hpoint (m : ℕ) :
      (roundingError m B - empiricalErrorMean B T)^4 ≤
        ((B : ℝ) / 2)^4 := by
    have habs := abs_centered_roundingError_common_period_le_half
      m B T hTpos hT
    calc
      (roundingError m B - empiricalErrorMean B T)^4 =
          |roundingError m B - empiricalErrorMean B T|^4 := by
            rcases le_total 0 (roundingError m B - empiricalErrorMean B T)
              with ht | ht
            · rw [abs_of_nonneg ht]
            · rw [abs_of_nonpos ht]
              ring
      _ ≤ ((B : ℝ) / 2)^4 := by gcongr
  unfold empiricalFourthMoment
  apply (div_le_iff₀ hTreal).2
  calc
    ∑ m ∈ Finset.range T,
      (roundingError m B - empiricalErrorMean B T)^4 ≤
        ∑ m ∈ Finset.range T, ((B : ℝ) / 2)^4 := by
          apply Finset.sum_le_sum
          intro m hm
          exact hpoint m
    _ = ((B : ℝ) / 2)^4 * (T : ℝ) := by simp [mul_comm]

/-- Conditional exponent improvement: a linear variance bound on full
periods would imply a cubic fourth-moment bound. The variance premise
has NOT been established here. -/
theorem empiricalFourthMoment_le_cubic_of_variance_le
    (B T : ℕ) (C : ℝ) (hTpos : 0 < T)
    (hT : ∀ d ∈ Finset.Icc 1 B, d ∣ T)
    (hVariance : empiricalSecondMoment B T ≤ C * (B : ℝ)) :
    empiricalFourthMoment B T ≤ (C / 4) * (B : ℝ)^3 := by
  calc
    empiricalFourthMoment B T ≤
      ((B : ℝ) / 2)^2 * empiricalSecondMoment B T :=
        empiricalFourthMoment_le_secondMoment_mul B T hTpos hT
    _ ≤ ((B : ℝ) / 2)^2 * (C * (B : ℝ)) := by
          apply mul_le_mul_of_nonneg_left hVariance
          positivity
    _ = (C / 4) * (B : ℝ)^3 := by ring

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

/-! ## Pointwise centering on arbitrary common periods -/

/-- The centering term of a modular fraction is independent of the
chosen positive multiple of its modulus. This is the exact pointwise
normal form used in the gcd covariance calculation. -/
theorem centeredModularFraction_common_period
    (m d T : ℕ) (hd : 0 < d) (hT : 0 < T) (hdT : d ∣ T) :
    centeredModularFraction m d T =
      (((m % d : ℕ) : ℝ) / (d : ℝ)) -
        (((d - 1 : ℕ) : ℝ) / (2 * (d : ℝ))) := by
  obtain ⟨q, hq⟩ := hdT
  have hqpos : 0 < q := by
    by_contra hn
    have hqzero : q = 0 := by omega
    simp [hqzero] at hq
    omega
  unfold centeredModularFraction
  rw [hq, Nat.mul_comm d q, modularFractionMean_multiple d q hd hqpos]

/-- The general full-period covariance reduces exactly to a finite sum of
explicitly centered modular residues. No gcd evaluation is asserted here. -/
theorem empiricalModularCovariance_common_period_explicit
    (a b T : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hTpos : 0 < T) (haT : a ∣ T) (hbT : b ∣ T) :
    empiricalModularCovariance a b T =
      (∑ m ∈ Finset.range T,
        ((((m % a : ℕ) : ℝ) / (a : ℝ)) -
          (((a - 1 : ℕ) : ℝ) / (2 * (a : ℝ)))) *
        ((((m % b : ℕ) : ℝ) / (b : ℝ)) -
          (((b - 1 : ℕ) : ℝ) / (2 * (b : ℝ))))) / (T : ℝ) := by
  unfold empiricalModularCovariance
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  rw [centeredModularFraction_common_period m a T ha hTpos haT,
    centeredModularFraction_common_period m b T hb hTpos hbT]

/-- A general finite covariance inequality obtained by summing
the pointwise nonnegative square of the difference of two centered
modular fractions. It applies even without a common-period condition. -/
theorem two_mul_empiricalModularCovariance_le_diagonal
    (a b H : ℕ) (hH : 0 < H) :
    2 * empiricalModularCovariance a b H ≤
      empiricalModularCovariance a a H +
        empiricalModularCovariance b b H := by
  have hHreal : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hpoint (m : ℕ) :
      2 * (centeredModularFraction m a H *
        centeredModularFraction m b H) ≤
        centeredModularFraction m a H *
          centeredModularFraction m a H +
        centeredModularFraction m b H *
          centeredModularFraction m b H := by
    nlinarith [sq_nonneg
      (centeredModularFraction m a H -
        centeredModularFraction m b H)]
  unfold empiricalModularCovariance
  calc
    2 * ((∑ m ∈ Finset.range H,
        centeredModularFraction m a H *
          centeredModularFraction m b H) / (H : ℝ)) =
      (∑ m ∈ Finset.range H,
        2 * (centeredModularFraction m a H *
          centeredModularFraction m b H)) / (H : ℝ) := by
        rw [← Finset.mul_sum]
        ring
    _ ≤ (∑ m ∈ Finset.range H,
        (centeredModularFraction m a H *
          centeredModularFraction m a H +
        centeredModularFraction m b H *
          centeredModularFraction m b H)) / (H : ℝ) := by
          apply div_le_div_of_nonneg_right
          · exact Finset.sum_le_sum (fun m hm => hpoint m)
          · exact le_of_lt hHreal
    _ = (∑ m ∈ Finset.range H,
          centeredModularFraction m a H *
            centeredModularFraction m a H) / (H : ℝ) +
        (∑ m ∈ Finset.range H,
          centeredModularFraction m b H *
            centeredModularFraction m b H) / (H : ℝ) := by
          rw [Finset.sum_add_distrib, add_div]

/-- The complementary bound, from the square of the sum of two
centered modular fractions. -/
theorem neg_diagonal_le_two_mul_empiricalModularCovariance
    (a b H : ℕ) (hH : 0 < H) :
    -(empiricalModularCovariance a a H +
        empiricalModularCovariance b b H) ≤
      2 * empiricalModularCovariance a b H := by
  have hHreal : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hpoint (m : ℕ) :
      -(centeredModularFraction m a H *
          centeredModularFraction m a H +
        centeredModularFraction m b H *
          centeredModularFraction m b H) ≤
        2 * (centeredModularFraction m a H *
          centeredModularFraction m b H) := by
    nlinarith [sq_nonneg
      (centeredModularFraction m a H +
        centeredModularFraction m b H)]
  have hsum :
      -(empiricalModularCovariance a a H +
        empiricalModularCovariance b b H) ≤
      2 * empiricalModularCovariance a b H := by
    unfold empiricalModularCovariance
    rw [← add_div]
    calc
      -(((∑ m ∈ Finset.range H,
          centeredModularFraction m a H * centeredModularFraction m a H) +
          (∑ m ∈ Finset.range H,
          centeredModularFraction m b H * centeredModularFraction m b H)) /
          (H : ℝ)) =
        (∑ m ∈ Finset.range H,
          -(centeredModularFraction m a H * centeredModularFraction m a H +
            centeredModularFraction m b H * centeredModularFraction m b H)) /
          (H : ℝ) := by
            rw [← Finset.sum_add_distrib, Finset.sum_neg_distrib, neg_div]
      _ ≤ (∑ m ∈ Finset.range H,
          2 * (centeredModularFraction m a H *
            centeredModularFraction m b H)) / (H : ℝ) := by
            apply div_le_div_of_nonneg_right
            · exact Finset.sum_le_sum (fun m hm => hpoint m)
            · exact le_of_lt hHreal
      _ = 2 * ((∑ m ∈ Finset.range H,
          centeredModularFraction m a H *
            centeredModularFraction m b H) / (H : ℝ)) := by
            rw [← Finset.mul_sum]
            ring
  exact hsum

/-- The product of two centered modular fractions is periodic in
any common multiple of their moduli, provided the averaging period
is itself a common multiple. -/
theorem centeredModularFraction_mul_add_common_period
    (m a b T : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hTpos : 0 < T) (haT : a ∣ T) (hbT : b ∣ T) :
    centeredModularFraction (m + T) a T *
      centeredModularFraction (m + T) b T =
    centeredModularFraction m a T *
      centeredModularFraction m b T := by
  rw [centeredModularFraction_common_period (m + T) a T ha hTpos haT,
    centeredModularFraction_common_period (m + T) b T hb hTpos hbT,
    centeredModularFraction_common_period m a T ha hTpos haT,
    centeredModularFraction_common_period m b T hb hTpos hbT]
  have hmoda : (m + T) % a = m % a := by
    simpa [Nat.add_mod, Nat.mod_eq_zero_of_dvd haT]
  have hmodb : (m + T) % b = m % b := by
    simpa [Nat.add_mod, Nat.mod_eq_zero_of_dvd hbT]
  rw [hmoda, hmodb]

/-- The least common multiple is a valid averaging period for the
explicit centered-residue covariance formula. This specializes the
common-period expansion, without yet evaluating the gcd correlation. -/
theorem empiricalModularCovariance_lcm_explicit
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    empiricalModularCovariance a b (Nat.lcm a b) =
      (∑ m ∈ Finset.range (Nat.lcm a b),
        ((((m % a : ℕ) : ℝ) / (a : ℝ)) -
          (((a - 1 : ℕ) : ℝ) / (2 * (a : ℝ)))) *
        ((((m % b : ℕ) : ℝ) / (b : ℝ)) -
          (((b - 1 : ℕ) : ℝ) / (2 * (b : ℝ))))) /
        (Nat.lcm a b : ℝ) := by
  exact empiricalModularCovariance_common_period_explicit
    a b (Nat.lcm a b) ha hb
    (Nat.lcm_pos ha hb) (Nat.dvd_lcm_left a b) (Nat.dvd_lcm_right a b)

/-- A finite sum of a periodic real-valued sequence over q complete
periods is q times its sum over one period. -/
private theorem sum_range_mul_of_period
    (f : ℕ → ℝ) (L q : ℕ) (hperiod : ∀ m, f (m + L) = f m) :
    (∑ m ∈ Finset.range (q * L), f m) =
      (q : ℝ) * ∑ m ∈ Finset.range L, f m := by
  have hshift (k m : ℕ) : f (k * L + m) = f m := by
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          f (k.succ * L + m) = f ((k * L + m) + L) := by
            congr 1
            simp only [Nat.succ_mul]
            omega
          _ = f (k * L + m) := hperiod _
          _ = f m := ih
  induction q with
  | zero => simp
  | succ q ih =>
      calc
        (∑ m ∈ Finset.range (q.succ * L), f m) =
            (∑ m ∈ Finset.range (q * L), f m) +
            (∑ m ∈ Finset.range L, f (q * L + m)) := by
              simpa only [Nat.succ_mul] using
                (Finset.sum_range_add f (q * L) L)
        _ = (∑ m ∈ Finset.range (q * L), f m) +
            (∑ m ∈ Finset.range L, f m) := by
              congr 1
              apply Finset.sum_congr rfl
              intro m hm
              exact hshift q m
        _ = (q.succ : ℝ) * ∑ m ∈ Finset.range L, f m := by
              rw [ih]
              push_cast
              ring

/-- Empirical modular covariance does not depend on which positive
common multiple of a and b is used as the averaging period. In
particular, it agrees with the covariance on lcm(a,b). -/
theorem empiricalModularCovariance_eq_lcm
    (a b T : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hTpos : 0 < T) (haT : a ∣ T) (hbT : b ∣ T) :
    empiricalModularCovariance a b T =
      empiricalModularCovariance a b (Nat.lcm a b) := by
  let L := Nat.lcm a b
  have hLpos : 0 < L := Nat.lcm_pos ha hb
  have haL : a ∣ L := Nat.dvd_lcm_left a b
  have hbL : b ∣ L := Nat.dvd_lcm_right a b
  obtain ⟨q, hq⟩ := (Nat.lcm_dvd haT hbT)
  have hqpos : 0 < q := by
    by_contra hn
    have hqzero : q = 0 := by omega
    simp [hqzero] at hq
    omega
  let f : ℕ → ℝ := fun m =>
    ((((m % a : ℕ) : ℝ) / (a : ℝ)) -
      (((a - 1 : ℕ) : ℝ) / (2 * (a : ℝ)))) *
    ((((m % b : ℕ) : ℝ) / (b : ℝ)) -
      (((b - 1 : ℕ) : ℝ) / (2 * (b : ℝ))))
  have hperiod (m : ℕ) : f (m + L) = f m := by
    dsimp [f]
    have hmoda : (m + L) % a = m % a := by
      simpa [Nat.add_mod, Nat.mod_eq_zero_of_dvd haL]
    have hmodb : (m + L) % b = m % b := by
      simpa [Nat.add_mod, Nat.mod_eq_zero_of_dvd hbL]
    rw [hmoda, hmodb]
  have hsum :
      (∑ m ∈ Finset.range T, f m) =
        (q : ℝ) * (∑ m ∈ Finset.range L, f m) := by
    rw [hq, Nat.mul_comm L q]
    exact sum_range_mul_of_period f L q hperiod
  have hqRne : (q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hqpos)
  have hLRne : (L : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hLpos)
  calc
    empiricalModularCovariance a b T =
        (∑ m ∈ Finset.range T, f m) / (T : ℝ) := by
          simpa only [f] using
            (empiricalModularCovariance_common_period_explicit
              a b T ha hb hTpos haT hbT)
    _ = ((q : ℝ) * (∑ m ∈ Finset.range L, f m)) /
        ((q : ℝ) * (L : ℝ)) := by
          rw [hsum, hq]
          push_cast
          rw [mul_comm (L : ℝ) (q : ℝ)]
    _ = (∑ m ∈ Finset.range L, f m) / (L : ℝ) := by
          apply (div_eq_div_iff (mul_ne_zero hqRne hLRne) hLRne).2
          ring
    _ = empiricalModularCovariance a b L := by
          symm
          simpa only [f] using
            (empiricalModularCovariance_common_period_explicit
              a b L ha hb hLpos haL hbL)

/-- The classical diagonal covariance formula holds on every positive
multiple of the modulus, not merely on the minimal period. -/
theorem empiricalModularCovariance_diagonal_common_period
    (d T : ℕ) (hd : 0 < d) (hTpos : 0 < T) (hdT : d ∣ T) :
    empiricalModularCovariance d d T =
      (((d : ℝ) ^ 2 - 1) / (12 * (d : ℝ) ^ 2)) := by
  rw [empiricalModularCovariance_eq_lcm d d T hd hd hTpos hdT hdT,
    Nat.lcm_self]
  exact empiricalModularCovariance_diagonal d hd

/-- The full Möbius-weighted variance is independent of the chosen
positive common period. This lifts the two-modulus covariance
period-invariance theorem through the exact quadratic-form expansion. -/
theorem empiricalSecondMoment_eq_of_common_periods
    (B T U : ℕ) (hTpos : 0 < T) (hUpos : 0 < U)
    (hT : ∀ d ∈ Finset.Icc 1 B, d ∣ T)
    (hU : ∀ d ∈ Finset.Icc 1 B, d ∣ U) :
    empiricalSecondMoment B T = empiricalSecondMoment B U := by
  rw [empiricalSecondMoment_eq_covariance_sum,
    empiricalSecondMoment_eq_covariance_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have haPos : 0 < a := (Finset.mem_Icc.mp ha).1
  have hbPos : 0 < b := (Finset.mem_Icc.mp hb).1
  rw [empiricalModularCovariance_eq_lcm a b T haPos hbPos hTpos
        (hT a ha) (hT b hb),
      empiricalModularCovariance_eq_lcm a b U haPos hbPos hUpos
        (hU a ha) (hU b hb)]

/-- Averaging the centered fourth power over several complete periods
has the same value as averaging over a single common period. -/
theorem empiricalFourthMoment_mul_common_period
    (B T q : ℕ) (hTpos : 0 < T) (hqpos : 0 < q)
    (hT : ∀ d ∈ Finset.Icc 1 B, d ∣ T) :
    empiricalFourthMoment B (q * T) = empiricalFourthMoment B T := by
  have hqTpos : 0 < q * T := Nat.mul_pos hqpos hTpos
  have hqT : ∀ d ∈ Finset.Icc 1 B, d ∣ q * T := by
    intro d hd
    obtain ⟨k, hk⟩ := hT d hd
    refine ⟨q * k, ?_⟩
    rw [hk]
    ring
  have hmean :
      empiricalErrorMean B (q * T) = empiricalErrorMean B T := by
    rw [empiricalErrorMean_common_period B (q * T) hqTpos hqT,
      empiricalErrorMean_common_period B T hTpos hT]
  let f : ℕ → ℝ := fun m =>
    (roundingError m B - empiricalErrorMean B T) ^ 4
  have hperiod (m : ℕ) : f (m + T) = f m := by
    dsimp [f]
    rw [roundingError_add_common_period m B T hT]
  have hsum :
      (∑ m ∈ Finset.range (q * T), f m) =
        (q : ℝ) * ∑ m ∈ Finset.range T, f m :=
    sum_range_mul_of_period f T q hperiod
  have hqRne : (q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hqpos)
  have hTRne : (T : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hTpos)
  unfold empiricalFourthMoment
  rw [hmean]
  change (∑ m ∈ Finset.range (q * T), f m) / (q * T : ℕ) =
    (∑ m ∈ Finset.range T, f m) / (T : ℝ)
  rw [hsum, Nat.cast_mul]
  apply (div_eq_div_iff (mul_ne_zero hqRne hTRne) hTRne).2
  ring

/-- The fourth moment is constant when the common averaging period is
replaced by any larger positive multiple. -/
theorem empiricalFourthMoment_eq_of_common_period_dvd
    (B T U : ℕ) (hTpos : 0 < T) (hUpos : 0 < U)
    (hT : ∀ d ∈ Finset.Icc 1 B, d ∣ T) (hTU : T ∣ U) :
    empiricalFourthMoment B T = empiricalFourthMoment B U := by
  obtain ⟨q, hU⟩ := hTU
  have hqpos : 0 < q := by
    by_contra hn
    have hqzero : q = 0 := by omega
    simp [hU, hqzero] at hUpos
  calc
    empiricalFourthMoment B T =
        empiricalFourthMoment B (q * T) :=
          (empiricalFourthMoment_mul_common_period B T q hTpos hqpos hT).symm
    _ = empiricalFourthMoment B U := by
          rw [hU, Nat.mul_comm T q]

/-- The centered fourth moment of the truncated Möbius rounding error
is independent of the chosen positive common period. No fourth-moment
asymptotic bound is claimed here. -/
theorem empiricalFourthMoment_eq_of_common_periods
    (B T U : ℕ) (hTpos : 0 < T) (hUpos : 0 < U)
    (hT : ∀ d ∈ Finset.Icc 1 B, d ∣ T)
    (hU : ∀ d ∈ Finset.Icc 1 B, d ∣ U) :
    empiricalFourthMoment B T = empiricalFourthMoment B U := by
  let L := Nat.lcm T U
  have hLpos : 0 < L := Nat.lcm_pos hTpos hUpos
  have hTL : T ∣ L := Nat.dvd_lcm_left T U
  have hUL : U ∣ L := Nat.dvd_lcm_right T U
  calc
    empiricalFourthMoment B T =
        empiricalFourthMoment B L :=
          empiricalFourthMoment_eq_of_common_period_dvd
            B T L hTpos hLpos hT hTL
    _ = empiricalFourthMoment B U :=
          (empiricalFourthMoment_eq_of_common_period_dvd
            B U L hUpos hLpos hU hUL).symm

/-! ## Arithmetic preparation for divisible-modulus covariance -/

/-- A centered modular fraction sums to zero on its complete modulus. -/
private theorem centeredModularFraction_sum_self_zero
    (a : ℕ) (ha : 0 < a) :
    (∑ m ∈ Finset.range a, centeredModularFraction m a a) = 0 := by
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  simp only [centeredModularFraction, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  unfold modularFractionMean
  field_simp [haR]
  ring

/-- If a periodic sequence has zero mean over a full period, then the
index-weighted sum over q periods is q times the basic weighted sum. -/
private theorem sum_range_mul_index_of_period_zero_mean
    (f : ℕ → ℝ) (L q : ℕ)
    (hperiod : ∀ m, f (m + L) = f m)
    (hzero : (∑ m ∈ Finset.range L, f m) = 0) :
    (∑ m ∈ Finset.range (q * L), f m * (m : ℝ)) =
      (q : ℝ) * ∑ m ∈ Finset.range L, f m * (m : ℝ) := by
  have hshift (k m : ℕ) : f (k * L + m) = f m := by
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          f (k.succ * L + m) = f ((k * L + m) + L) := by
            congr 1
            simp only [Nat.succ_mul]
            omega
          _ = f (k * L + m) := hperiod _
          _ = f m := ih
  have hblock (k : ℕ) :
      (∑ m ∈ Finset.range L, f (k * L + m) * ((k * L + m : ℕ) : ℝ)) =
        ∑ m ∈ Finset.range L, f m * (m : ℝ) := by
    calc
      (∑ m ∈ Finset.range L, f (k * L + m) * ((k * L + m : ℕ) : ℝ)) =
          ∑ m ∈ Finset.range L,
            (f m * (m : ℝ) + ((k * L : ℕ) : ℝ) * f m) := by
              apply Finset.sum_congr rfl
              intro m hm
              rw [hshift, Nat.cast_add]
              ring
      _ = (∑ m ∈ Finset.range L, f m * (m : ℝ)) +
          ((k * L : ℕ) : ℝ) * (∑ m ∈ Finset.range L, f m) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ m ∈ Finset.range L, f m * (m : ℝ) := by
            rw [hzero]
            ring
  induction q with
  | zero => simp
  | succ q ih =>
      calc
        (∑ m ∈ Finset.range (q.succ * L), f m * (m : ℝ)) =
            (∑ m ∈ Finset.range (q * L), f m * (m : ℝ)) +
            (∑ m ∈ Finset.range L,
              f (q * L + m) * ((q * L + m : ℕ) : ℝ)) := by
                simpa only [Nat.succ_mul] using
                  (Finset.sum_range_add
                    (fun m => f m * (m : ℝ)) (q * L) L)
        _ = (∑ m ∈ Finset.range (q * L), f m * (m : ℝ)) +
            (∑ m ∈ Finset.range L, f m * (m : ℝ)) := by rw [hblock]
        _ = (q.succ : ℝ) * ∑ m ∈ Finset.range L, f m * (m : ℝ) := by
              rw [ih]
              push_cast
              ring

/-- For a positive divisor a of b, covariance with modulus b on one
full b-period is the diagonal covariance at a scaled by a/b. -/
theorem empiricalModularCovariance_dvd_right_base
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a ∣ b) :
    empiricalModularCovariance a b b =
      ((a : ℝ) / (b : ℝ)) * empiricalModularCovariance a a a := by
  obtain ⟨q, hq⟩ := hab
  have hbq : b = q * a := by simpa only [Nat.mul_comm] using hq
  have hqpos : 0 < q := by
    by_contra hn
    have hqzero : q = 0 := by omega
    simp [hqzero] at hbq
    omega
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hqpos)
  let f : ℕ → ℝ := fun m => centeredModularFraction m a a
  have hperiod (m : ℕ) : f (m + a) = f m := by
    dsimp [f]
    rw [centeredModularFraction_common_period (m + a) a a ha ha (dvd_refl a),
      centeredModularFraction_common_period m a a ha ha (dvd_refl a)]
    have hmod : (m + a) % a = m % a := by
      simpa [Nat.add_mod]
    rw [hmod]
  have hzero : (∑ m ∈ Finset.range a, f m) = 0 :=
    centeredModularFraction_sum_self_zero a ha
  have hzerob : (∑ m ∈ Finset.range b, f m) = 0 := by
    rw [hbq, sum_range_mul_of_period f a q hperiod, hzero]
    ring
  have hcenter (m : ℕ) : centeredModularFraction m a b = f m := by
    dsimp [f]
    rw [centeredModularFraction_common_period m a b ha hb (by
      exact ⟨q, by simpa only [Nat.mul_comm] using hq⟩),
      centeredModularFraction_common_period m a a ha ha (dvd_refl a)]
  have hfrac (m : ℕ) (hm : m ∈ Finset.range a) :
      f m = (m : ℝ) / (a : ℝ) -
        (((a - 1 : ℕ) : ℝ) / (2 * (a : ℝ))) := by
    dsimp [f]
    rw [centeredModularFraction_common_period m a a ha ha (dvd_refl a),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hm)]
  have hweighted_diag :
      (∑ m ∈ Finset.range a, f m * (m : ℝ)) =
        (a : ℝ) * ∑ m ∈ Finset.range a, f m * f m := by
    have hpoint (m : ℕ) (hm : m ∈ Finset.range a) :
        f m * (m : ℝ) =
          (a : ℝ) * (f m * f m) +
            (((a - 1 : ℕ) : ℝ) / 2) * f m := by
      rw [hfrac m hm]
      field_simp [haR]
      <;> ring
    calc
      (∑ m ∈ Finset.range a, f m * (m : ℝ)) =
          ∑ m ∈ Finset.range a,
            ((a : ℝ) * (f m * f m) +
              (((a - 1 : ℕ) : ℝ) / 2) * f m) := by
                apply Finset.sum_congr rfl
                intro m hm
                exact hpoint m hm
      _ = (a : ℝ) * (∑ m ∈ Finset.range a, f m * f m) +
          (((a - 1 : ℕ) : ℝ) / 2) *
            (∑ m ∈ Finset.range a, f m) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = (a : ℝ) * ∑ m ∈ Finset.range a, f m * f m := by
            rw [hzero]
            ring
  have hweightedb :
      (∑ m ∈ Finset.range b, f m * (m : ℝ)) =
        (q : ℝ) * (∑ m ∈ Finset.range a, f m * (m : ℝ)) := by
    rw [hbq]
    exact sum_range_mul_index_of_period_zero_mean f a q hperiod hzero
  have hprod :
      (∑ m ∈ Finset.range b,
        centeredModularFraction m a b * centeredModularFraction m b b) =
      (∑ m ∈ Finset.range b, f m * (m : ℝ)) / (b : ℝ) := by
    let c : ℝ := (((b - 1 : ℕ) : ℝ) / (2 * (b : ℝ)))
    calc
      (∑ m ∈ Finset.range b,
        centeredModularFraction m a b * centeredModularFraction m b b) =
        ∑ m ∈ Finset.range b, f m * ((m : ℝ) / (b : ℝ) - c) := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [hcenter m,
            centeredModularFraction_common_period m b b hb hb (dvd_refl b),
            Nat.mod_eq_of_lt (Finset.mem_range.mp hm)]
      _ = (∑ m ∈ Finset.range b,
          ((f m * (m : ℝ)) / (b : ℝ) - c * f m)) := by
            apply Finset.sum_congr rfl
            intro m hm
            ring
      _ = (∑ m ∈ Finset.range b, f m * (m : ℝ)) / (b : ℝ) -
          c * (∑ m ∈ Finset.range b, f m) := by
            rw [Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]
      _ = (∑ m ∈ Finset.range b, f m * (m : ℝ)) / (b : ℝ) := by
            rw [hzerob]
            ring
  have hcovexpr :
      empiricalModularCovariance a b b =
        ((∑ m ∈ Finset.range b, f m * (m : ℝ)) / (b : ℝ)) /
          (b : ℝ) := by
    unfold empiricalModularCovariance
    rw [hprod]
  have hdiagcov :
      empiricalModularCovariance a a a =
        (∑ m ∈ Finset.range a, f m * f m) / (a : ℝ) := rfl
  calc
    empiricalModularCovariance a b b =
        ((∑ m ∈ Finset.range b, f m * (m : ℝ)) / (b : ℝ)) /
          (b : ℝ) := hcovexpr
    _ = (((q : ℝ) * ((a : ℝ) *
          (∑ m ∈ Finset.range a, f m * f m))) / (b : ℝ)) /
          (b : ℝ) := by rw [hweightedb, hweighted_diag]
    _ = ((a : ℝ) / (b : ℝ)) *
          empiricalModularCovariance a a a := by
            rw [hdiagcov, hbq]
            push_cast
            field_simp [haR, hqR]
            <;> ring

/-- The exact gcd covariance formula for the non-diagonal family
a dividing b, over any positive common averaging period. -/
theorem empiricalModularCovariance_gcd_of_dvd
    (a b T : ℕ) (ha : 0 < a) (hb : 0 < b) (hTpos : 0 < T)
    (hab : a ∣ b) (hbT : b ∣ T) :
    empiricalModularCovariance a b T =
      (((Nat.gcd a b : ℝ) ^ 2 - 1) /
        (12 * (a : ℝ) * (b : ℝ))) := by
  have haT : a ∣ T := dvd_trans hab hbT
  have hcov : empiricalModularCovariance a b T =
      empiricalModularCovariance a b b := by
    calc
      empiricalModularCovariance a b T =
          empiricalModularCovariance a b (Nat.lcm a b) :=
            empiricalModularCovariance_eq_lcm a b T
              ha hb hTpos haT hbT
      _ = empiricalModularCovariance a b b :=
            (empiricalModularCovariance_eq_lcm a b b
              ha hb hb hab (dvd_refl b)).symm
  have hgcd : Nat.gcd a b = a := Nat.gcd_eq_left_iff_dvd.mpr hab
  rw [hcov, empiricalModularCovariance_dvd_right_base a b ha hb hab,
    empiricalModularCovariance_diagonal a ha, hgcd]
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  field_simp [haR, hbR]
  <;> ring

/-- The exact gcd covariance formula also holds when b divides a,
by symmetry of the covariance. -/
theorem empiricalModularCovariance_gcd_of_dvd_left
    (a b T : ℕ) (ha : 0 < a) (hb : 0 < b) (hTpos : 0 < T)
    (hba : b ∣ a) (haT : a ∣ T) :
    empiricalModularCovariance a b T =
      (((Nat.gcd a b : ℝ) ^ 2 - 1) /
        (12 * (a : ℝ) * (b : ℝ))) := by
  calc
    empiricalModularCovariance a b T =
        empiricalModularCovariance b a T :=
          empiricalModularCovariance_comm a b T
    _ = (((Nat.gcd b a : ℝ) ^ 2 - 1) /
        (12 * (b : ℝ) * (a : ℝ))) :=
          empiricalModularCovariance_gcd_of_dvd b a T hb ha hTpos hba haT
    _ = (((Nat.gcd a b : ℝ) ^ 2 - 1) /
        (12 * (a : ℝ) * (b : ℝ))) := by
          rw [Nat.gcd_comm b a]
          congr 1
          ring

/-- The full gcd identity for all pairs of positive comparable moduli:
either a divides b, or b divides a. -/
theorem empiricalModularCovariance_gcd_of_comparable
    (a b T : ℕ) (ha : 0 < a) (hb : 0 < b) (hTpos : 0 < T)
    (hcmp : a ∣ b ∨ b ∣ a) (haT : a ∣ T) (hbT : b ∣ T) :
    empiricalModularCovariance a b T =
      (((Nat.gcd a b : ℝ) ^ 2 - 1) /
        (12 * (a : ℝ) * (b : ℝ))) := by
  rcases hcmp with hab | hba
  · exact empiricalModularCovariance_gcd_of_dvd
      a b T ha hb hTpos hab hbT
  · exact empiricalModularCovariance_gcd_of_dvd_left
      a b T ha hb hTpos hba haT

/-! ## A coprime off-diagonal family: modulus two and odd moduli -/

/-- On a common period of two and an odd modulus, shifting by that odd
modulus reverses the centered fraction modulo two. -/
theorem centeredModularFraction_two_add_odd
    (m b : ℕ) (hbodd : b % 2 = 1) :
    centeredModularFraction (m + b) 2 (2 * b) =
      -centeredModularFraction m 2 (2 * b) := by
  have hb : 0 < b := by omega
  have hTpos : 0 < 2 * b := by omega
  have h2T : 2 ∣ 2 * b := ⟨b, rfl⟩
  rw [centeredModularFraction_common_period (m + b) 2 (2 * b)
        (by norm_num) hTpos h2T,
      centeredModularFraction_common_period m 2 (2 * b)
        (by norm_num) hTpos h2T]
  have hmod : (m + b) % 2 + m % 2 = 1 := by
    have hsum : (m + b) % 2 = (m % 2 + 1) % 2 := by
      simp [Nat.add_mod, hbodd]
    have hm : m % 2 < 2 := Nat.mod_lt m (by omega)
    omega
  have hmodR : (((m + b) % 2 : ℕ) : ℝ) + ((m % 2 : ℕ) : ℝ) = 1 := by
    exact_mod_cast hmod
  norm_num
  linarith

/-- Translating by b leaves the centered fraction modulo b unchanged,
even when the averaging period is twice b. -/
theorem centeredModularFraction_self_add_on_double
    (m b : ℕ) :
    centeredModularFraction (m + b) b (2 * b) =
      centeredModularFraction m b (2 * b) := by
  unfold centeredModularFraction
  have hmod : (m + b) % b = m % b := by
    simp [Nat.add_mod]
  rw [hmod]

/-- The covariance of fractions modulo two and an odd modulus is zero
over the double period, by cancellation between its two b-blocks. -/
theorem empiricalModularCovariance_two_odd_double_zero
    (b : ℕ) (hbodd : b % 2 = 1) :
    empiricalModularCovariance 2 b (2 * b) = 0 := by
  let f : ℕ → ℝ := fun m =>
    centeredModularFraction m 2 (2 * b) *
      centeredModularFraction m b (2 * b)
  have hanti (m : ℕ) : f (m + b) = -f m := by
    dsimp [f]
    rw [centeredModularFraction_two_add_odd m b hbodd,
      centeredModularFraction_self_add_on_double m b]
    ring
  have hblock :
      (∑ m ∈ Finset.range b, f (b + m)) =
        -(∑ m ∈ Finset.range b, f m) := by
    calc
      (∑ m ∈ Finset.range b, f (b + m)) =
          ∑ m ∈ Finset.range b, -(f m) := by
            apply Finset.sum_congr rfl
            intro m hm
            simpa only [Nat.add_comm] using hanti m
      _ = -(∑ m ∈ Finset.range b, f m) := by
            rw [Finset.sum_neg_distrib]
  have hsum : (∑ m ∈ Finset.range (2 * b), f m) = 0 := by
    have hadd : b + b = 2 * b := by omega
    rw [← hadd, Finset.sum_range_add f b b, hblock]
    ring
  unfold empiricalModularCovariance
  change (∑ m ∈ Finset.range (2 * b), f m) / (2 * b : ℕ) = 0
  rw [hsum]
  simp

/-- A new non-comparable gcd-covariance family: if b is odd, its
centered modular fraction is uncorrelated with modulus two over every
positive common averaging period. -/
theorem empiricalModularCovariance_gcd_two_odd
    (b T : ℕ) (hbodd : b % 2 = 1) (hTpos : 0 < T)
    (h2T : 2 ∣ T) (hbT : b ∣ T) :
    empiricalModularCovariance 2 b T =
      (((Nat.gcd 2 b : ℝ) ^ 2 - 1) /
        (12 * (2 : ℝ) * (b : ℝ))) := by
  have hb : 0 < b := by omega
  have h2bpos : 0 < 2 * b := by omega
  have h2_2b : 2 ∣ 2 * b := ⟨b, rfl⟩
  have hb_2b : b ∣ 2 * b := ⟨2, by omega⟩
  have hcov :
      empiricalModularCovariance 2 b T =
        empiricalModularCovariance 2 b (2 * b) := by
    calc
      empiricalModularCovariance 2 b T =
          empiricalModularCovariance 2 b (Nat.lcm 2 b) :=
            empiricalModularCovariance_eq_lcm 2 b T
              (by norm_num) hb hTpos h2T hbT
      _ = empiricalModularCovariance 2 b (2 * b) :=
            (empiricalModularCovariance_eq_lcm 2 b (2 * b)
              (by norm_num) hb h2bpos h2_2b hb_2b).symm
  have hgcd : Nat.gcd 2 b = 1 := by
    have hdiv2 : Nat.gcd 2 b ∣ 2 := Nat.gcd_dvd_left 2 b
    have hdivb : Nat.gcd 2 b ∣ b := Nat.gcd_dvd_right 2 b
    have hne : Nat.gcd 2 b ≠ 0 := by
      intro hzero
      have : b = 0 := by simpa [hzero] using hdivb
      omega
    have hle : Nat.gcd 2 b ≤ 2 :=
      Nat.le_of_dvd (by omega) hdiv2
    have hnot2 : Nat.gcd 2 b ≠ 2 := by
      intro hh
      have h : 2 ∣ b := by simpa [hh] using hdivb
      have hmod : b % 2 = 0 := Nat.mod_eq_zero_of_dvd h
      omega
    omega
  rw [hcov, empiricalModularCovariance_two_odd_double_zero b hbodd,
    hgcd]
  norm_num

/-- The full gcd-covariance identity holds whenever the first
positive modulus is two, with no parity restriction on the other
modulus. Even moduli use the divisibility case; odd moduli use
the two-block cancellation theorem. -/
theorem empiricalModularCovariance_gcd_two_any
    (b T : ℕ) (hb : 0 < b) (hTpos : 0 < T)
    (h2T : 2 ∣ T) (hbT : b ∣ T) :
    empiricalModularCovariance 2 b T =
      (((Nat.gcd 2 b : ℝ) ^ 2 - 1) /
        (12 * (2 : ℝ) * (b : ℝ))) := by
  by_cases heven : b % 2 = 0
  · have h2b : 2 ∣ b := Nat.dvd_of_mod_eq_zero heven
    exact empiricalModularCovariance_gcd_of_dvd
      2 b T (by norm_num) hb hTpos h2b hbT
  · have hodd : b % 2 = 1 := by
      have hlt : b % 2 < 2 := Nat.mod_lt b (by norm_num)
      omega
    exact empiricalModularCovariance_gcd_two_odd b T hodd hTpos h2T hbT

/-- The symmetric all-moduli family: exact covariance when the second
modulus is two. -/
theorem empiricalModularCovariance_gcd_any_two
    (a T : ℕ) (ha : 0 < a) (hTpos : 0 < T)
    (haT : a ∣ T) (h2T : 2 ∣ T) :
    empiricalModularCovariance a 2 T =
      (((Nat.gcd a 2 : ℝ) ^ 2 - 1) /
        (12 * (a : ℝ) * (2 : ℝ))) := by
  calc
    empiricalModularCovariance a 2 T =
        empiricalModularCovariance 2 a T :=
          empiricalModularCovariance_comm a 2 T
    _ = (((Nat.gcd 2 a : ℝ) ^ 2 - 1) /
        (12 * (2 : ℝ) * (a : ℝ))) :=
          empiricalModularCovariance_gcd_two_any a T ha hTpos h2T haT
    _ = (((Nat.gcd a 2 : ℝ) ^ 2 - 1) /
        (12 * (a : ℝ) * (2 : ℝ))) := by
          rw [Nat.gcd_comm 2 a]
          congr 1
          ring

/-! ## Coprime correlations with modulus three -/

/-- Three translated residues modulo three run through all three
residue classes whenever the shift is not divisible by three. -/
private theorem mod_three_shift_residue_sum
    (m b : ℕ) (hb : b % 3 ≠ 0) :
    m % 3 + (b + m) % 3 + ((b + b) + m) % 3 = 3 := by
  have hfirst : m % 3 < 3 := Nat.mod_lt m (by omega)
  have hsecond : b % 3 < 3 := Nat.mod_lt b (by omega)
  have hcase : b % 3 = 1 ∨ b % 3 = 2 := by omega
  have hshift1 : (b + m) % 3 = (b % 3 + m % 3) % 3 :=
    Nat.add_mod b m 3
  have hshift2 : ((b + b) + m) % 3 =
      ((b % 3 + b % 3) % 3 + m % 3) % 3 := by
    calc
      ((b + b) + m) % 3 =
          ((b + b) % 3 + m % 3) % 3 :=
            Nat.add_mod (b + b) m 3
      _ = ((b % 3 + b % 3) % 3 + m % 3) % 3 := by
            rw [Nat.add_mod b b 3]
  rw [hshift1, hshift2]
  rcases hcase with hcase | hcase
  · rw [hcase]
    omega
  · rw [hcase]
    omega

/-- The three centered fractions modulo three cancel after translating
by b and 2b, when b is coprime to three. -/
theorem centeredModularFraction_three_block_sum_zero
    (m b : ℕ) (hb : b % 3 ≠ 0) :
    centeredModularFraction m 3 (3 * b) +
      centeredModularFraction (b + m) 3 (3 * b) +
      centeredModularFraction ((b + b) + m) 3 (3 * b) = 0 := by
  have hbpos : 0 < b := by omega
  have hTpos : 0 < 3 * b := by omega
  have h3T : 3 ∣ 3 * b := ⟨b, rfl⟩
  rw [centeredModularFraction_common_period m 3 (3 * b)
        (by omega) hTpos h3T,
      centeredModularFraction_common_period (b + m) 3 (3 * b)
        (by omega) hTpos h3T,
      centeredModularFraction_common_period ((b + b) + m) 3 (3 * b)
        (by omega) hTpos h3T]
  have hres : m % 3 + (b + m) % 3 +
      ((b + b) + m) % 3 = 3 :=
    mod_three_shift_residue_sum m b hb
  have hresR :
      ((m % 3 : ℕ) : ℝ) + (((b + m) % 3 : ℕ) : ℝ) +
        ((((b + b) + m) % 3 : ℕ) : ℝ) = 3 := by
    exact_mod_cast hres
  norm_num
  linarith

/-- The covariance modulo three and a modulus prime to three vanishes
on their product period, by grouping the sum into three b-blocks. -/
theorem empiricalModularCovariance_three_coprime_product_zero
    (b : ℕ) (hb : b % 3 ≠ 0) :
    empiricalModularCovariance 3 b (3 * b) = 0 := by
  let f : ℕ → ℝ := fun m =>
    centeredModularFraction m 3 (3 * b) *
      centeredModularFraction m b (3 * b)
  have hblock (m : ℕ) :
      f m + f (b + m) + f ((b + b) + m) = 0 := by
    have hb1 : centeredModularFraction (b + m) b (3 * b) =
        centeredModularFraction m b (3 * b) := by
      simp [centeredModularFraction, Nat.add_mod]
    have hb2 : centeredModularFraction ((b + b) + m) b (3 * b) =
        centeredModularFraction m b (3 * b) := by
      simp [centeredModularFraction, Nat.add_mod]
    dsimp [f]
    rw [hb1, hb2]
    have hs := centeredModularFraction_three_block_sum_zero m b hb
    calc
      centeredModularFraction m 3 (3 * b) *
          centeredModularFraction m b (3 * b) +
        centeredModularFraction (b + m) 3 (3 * b) *
          centeredModularFraction m b (3 * b) +
        centeredModularFraction ((b + b) + m) 3 (3 * b) *
          centeredModularFraction m b (3 * b) =
        (centeredModularFraction m 3 (3 * b) +
          centeredModularFraction (b + m) 3 (3 * b) +
          centeredModularFraction ((b + b) + m) 3 (3 * b)) *
            centeredModularFraction m b (3 * b) := by ring
      _ = 0 := by rw [hs]; ring
  have hsum : (∑ m ∈ Finset.range (3 * b), f m) = 0 := by
    have hlen : 3 * b = (b + b) + b := by omega
    calc
      (∑ m ∈ Finset.range (3 * b), f m) =
          ∑ m ∈ Finset.range b,
            (f m + f (b + m) + f ((b + b) + m)) := by
              rw [hlen, Finset.sum_range_add f (b + b) b,
                Finset.sum_range_add f b b]
              simp only [Finset.sum_add_distrib]
      _ = 0 := by simp [hblock]
  unfold empiricalModularCovariance
  change (∑ m ∈ Finset.range (3 * b), f m) / (3 * b : ℕ) = 0
  rw [hsum]
  simp

/-- The exact gcd formula for a genuinely non-comparable family:
three and any positive modulus not divisible by three. -/
theorem empiricalModularCovariance_gcd_three_coprime
    (b T : ℕ) (hb : b % 3 ≠ 0) (hTpos : 0 < T)
    (h3T : 3 ∣ T) (hbT : b ∣ T) :
    empiricalModularCovariance 3 b T =
      (((Nat.gcd 3 b : ℝ) ^ 2 - 1) /
        (12 * (3 : ℝ) * (b : ℝ))) := by
  have hbpos : 0 < b := by omega
  have h3bpos : 0 < 3 * b := by omega
  have h3_3b : 3 ∣ 3 * b := ⟨b, rfl⟩
  have hb_3b : b ∣ 3 * b := ⟨3, by omega⟩
  have hcov :
      empiricalModularCovariance 3 b T =
        empiricalModularCovariance 3 b (3 * b) := by
    calc
      empiricalModularCovariance 3 b T =
          empiricalModularCovariance 3 b (Nat.lcm 3 b) :=
            empiricalModularCovariance_eq_lcm 3 b T
              (by omega) hbpos hTpos h3T hbT
      _ = empiricalModularCovariance 3 b (3 * b) :=
            (empiricalModularCovariance_eq_lcm 3 b (3 * b)
              (by omega) hbpos h3bpos h3_3b hb_3b).symm
  have hgcd : Nat.gcd 3 b = 1 := by
    have hdiv3 : Nat.gcd 3 b ∣ 3 := Nat.gcd_dvd_left 3 b
    have hdivb : Nat.gcd 3 b ∣ b := Nat.gcd_dvd_right 3 b
    have hne : Nat.gcd 3 b ≠ 0 := by
      intro hzero
      have : b = 0 := by simpa [hzero] using hdivb
      omega
    have hle : Nat.gcd 3 b ≤ 3 :=
      Nat.le_of_dvd (by omega) hdiv3
    have hnot2 : Nat.gcd 3 b ≠ 2 := by
      intro htwo
      have : 2 ∣ 3 := by simpa [htwo] using hdiv3
      norm_num at this
    have hnot3 : Nat.gcd 3 b ≠ 3 := by
      intro hthree
      have h : 3 ∣ b := by simpa [hthree] using hdivb
      exact hb (Nat.mod_eq_zero_of_dvd h)
    omega
  rw [hcov, empiricalModularCovariance_three_coprime_product_zero b hb,
    hgcd]
  norm_num

/-- The gcd covariance identity for modulus three and any positive
second modulus. The divisible case uses the earlier general theorem;
the coprime case uses cancellation over three translated blocks. -/
theorem empiricalModularCovariance_gcd_three_any
    (b T : ℕ) (hb : 0 < b) (hTpos : 0 < T)
    (h3T : 3 ∣ T) (hbT : b ∣ T) :
    empiricalModularCovariance 3 b T =
      (((Nat.gcd 3 b : ℝ) ^ 2 - 1) /
        (12 * (3 : ℝ) * (b : ℝ))) := by
  by_cases hdiv : b % 3 = 0
  · have h3b : 3 ∣ b := Nat.dvd_of_mod_eq_zero hdiv
    exact empiricalModularCovariance_gcd_of_dvd
      3 b T (by norm_num) hb hTpos h3b hbT
  · exact empiricalModularCovariance_gcd_three_coprime
      b T hdiv hTpos h3T hbT

/-- The symmetric all-moduli family for the fixed modulus three. -/
theorem empiricalModularCovariance_gcd_any_three
    (a T : ℕ) (ha : 0 < a) (hTpos : 0 < T)
    (haT : a ∣ T) (h3T : 3 ∣ T) :
    empiricalModularCovariance a 3 T =
      (((Nat.gcd a 3 : ℝ) ^ 2 - 1) /
        (12 * (a : ℝ) * (3 : ℝ))) := by
  calc
    empiricalModularCovariance a 3 T =
        empiricalModularCovariance 3 a T :=
          empiricalModularCovariance_comm a 3 T
    _ = (((Nat.gcd 3 a : ℝ) ^ 2 - 1) /
        (12 * (3 : ℝ) * (a : ℝ))) :=
          empiricalModularCovariance_gcd_three_any
            a T ha hTpos h3T haT
    _ = (((Nat.gcd a 3 : ℝ) ^ 2 - 1) /
        (12 * (a : ℝ) * (3 : ℝ))) := by
          rw [Nat.gcd_comm 3 a]
          congr 1
          ring

/-! ## Chinese remainder theorem: uniform coprime residue pairs -/

/-- The CRT transforms every correlation of functions of two coprime
residue coordinates into the product of their separate complete sums.
This is a finite, exact factorization, not yet the gcd covariance
formula for arbitrary non-coprime moduli. -/
theorem coprime_zmod_product_sum_factorization
    (a b : ℕ) [NeZero a] [NeZero b] [NeZero (a * b)]
    (hcop : a.Coprime b)
    (f : ZMod a → ℝ) (g : ZMod b → ℝ) :
    (∑ m : ZMod (a * b),
      f ((ZMod.chineseRemainder hcop m).1) *
        g ((ZMod.chineseRemainder hcop m).2)) =
      (∑ r : ZMod a, f r) * (∑ s : ZMod b, g s) := by
  let e : ZMod (a * b) ≃ ZMod a × ZMod b :=
    (ZMod.chineseRemainder hcop).toEquiv
  change (∑ m : ZMod (a * b), f (e m).1 * g (e m).2) = _
  rw [Equiv.sum_comp e
    (fun p : ZMod a × ZMod b => f p.1 * g p.2)]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

/-- A centered function of the first residue coordinate is orthogonal
to every function of the second coordinate, for coprime moduli.
This is the essential CRT cancellation mechanism. -/
theorem coprime_zmod_centered_orthogonality
    (a b : ℕ) [NeZero a] [NeZero b] [NeZero (a * b)]
    (hcop : a.Coprime b)
    (f : ZMod a → ℝ) (g : ZMod b → ℝ)
    (hcenter : (∑ r : ZMod a, f r) = 0) :
    (∑ m : ZMod (a * b),
      f ((ZMod.chineseRemainder hcop m).1) *
        g ((ZMod.chineseRemainder hcop m).2)) = 0 := by
  rw [coprime_zmod_product_sum_factorization a b hcop f g,
    hcenter, zero_mul]

/-- CRT projections agree with the original natural-number residues.
This bridges Mathlib's ring-equivalence formulation of CRT with the
modular fractions used in this project. -/
theorem coprime_zmod_chineseRemainder_nat_coordinates
    (a b m : ℕ) (hcop : a.Coprime b) :
    (ZMod.chineseRemainder hcop (m : ZMod (a * b))).1 =
        (m : ZMod a) ∧
      (ZMod.chineseRemainder hcop (m : ZMod (a * b))).2 =
        (m : ZMod b) := by
  constructor <;> simp

/-- Summing a real function of the standard residue representative
over ZMod n equals summing it over the natural range 0,…,n−1. -/
private theorem sum_zmod_val_eq_sum_range
    (n : ℕ) [NeZero n] (hn : 0 < n) (f : ℕ → ℝ) :
    (∑ x : ZMod n, f x.val) =
      ∑ m ∈ Finset.range n, f m := by
  cases n with
  | zero => omega
  | succ n =>
      change (∑ x : Fin (n + 1), f x.val) =
        ∑ m ∈ Finset.range (n + 1), f m
      exact Fin.sum_univ_eq_sum_range f (n + 1)

/-- The centered real representative of any positive residue ring has
zero complete-period sum. This provides the CRT input for covariance. -/
theorem centered_zmod_residue_sum_zero
    (a : ℕ) [NeZero a] (ha : 0 < a) :
    (∑ r : ZMod a,
      ((r.val : ℝ) / (a : ℝ) -
        (((a - 1 : ℕ) : ℝ) / (2 * (a : ℝ))))) = 0 := by
  rw [sum_zmod_val_eq_sum_range a ha
    (fun m => (m : ℝ) / (a : ℝ) -
      (((a - 1 : ℕ) : ℝ) / (2 * (a : ℝ))))]
  calc
    (∑ m ∈ Finset.range a,
      ((m : ℝ) / (a : ℝ) -
        (((a - 1 : ℕ) : ℝ) / (2 * (a : ℝ))))) =
        ∑ m ∈ Finset.range a, centeredModularFraction m a a := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [centeredModularFraction_common_period m a a
            ha ha (dvd_refl a),
            Nat.mod_eq_of_lt (Finset.mem_range.mp hm)]
    _ = 0 := centeredModularFraction_sum_self_zero a ha

/-- For any positive coprime moduli, the CRT-indexed centered residue
correlation vanishes exactly, without fixing either modulus.
The connection to empiricalModularCovariance still needs to be
expressed in the natural-number indexing of that definition. -/
theorem coprime_zmod_centered_residue_product_zero
    (a b : ℕ) [NeZero a] [NeZero b] [NeZero (a * b)]
    (ha : 0 < a) (hcop : a.Coprime b) :
    (∑ x : ZMod (a * b),
      (((((ZMod.chineseRemainder hcop x).1.val : ℕ) : ℝ) /
          (a : ℝ)) -
        (((a - 1 : ℕ) : ℝ) / (2 * (a : ℝ)))) *
      (((((ZMod.chineseRemainder hcop x).2.val : ℕ) : ℝ) /
          (b : ℝ)) -
        (((b - 1 : ℕ) : ℝ) / (2 * (b : ℝ))))) = 0 := by
  exact coprime_zmod_centered_orthogonality a b hcop
    (fun r => (r.val : ℝ) / (a : ℝ) -
      (((a - 1 : ℕ) : ℝ) / (2 * (a : ℝ))))
    (fun s => (s.val : ℝ) / (b : ℝ) -
      (((b - 1 : ℕ) : ℝ) / (2 * (b : ℝ))))
    (centered_zmod_residue_sum_zero a ha)

/-- CRT gives zero for the product of explicitly centered modular
fractions on a natural-number period of length a*b. This is the
bridge from ZMod to the covariance sum used by the project. -/
theorem coprime_centered_modular_sum_zero
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b) :
    (∑ m ∈ Finset.range (a * b),
      (((((m % a : ℕ) : ℝ) / (a : ℝ)) -
          (((a - 1 : ℕ) : ℝ) / (2 * (a : ℝ)))) *
        ((((m % b : ℕ) : ℝ) / (b : ℝ)) -
          (((b - 1 : ℕ) : ℝ) / (2 * (b : ℝ)))))) = 0 := by
  have habpos : 0 < a * b := Nat.mul_pos ha hb
  letI : NeZero a := ⟨Nat.ne_of_gt ha⟩
  letI : NeZero b := ⟨Nat.ne_of_gt hb⟩
  letI : NeZero (a * b) := ⟨Nat.ne_of_gt habpos⟩
  let f : ℕ → ℝ := fun m =>
    ((((m % a : ℕ) : ℝ) / (a : ℝ)) -
      (((a - 1 : ℕ) : ℝ) / (2 * (a : ℝ)))) *
    ((((m % b : ℕ) : ℝ) / (b : ℝ)) -
      (((b - 1 : ℕ) : ℝ) / (2 * (b : ℝ))))
  have hcoord_a (x : ZMod (a * b)) :
      (ZMod.chineseRemainder hcop x).1.val = x.val % a := by
    have heq :
        (ZMod.chineseRemainder hcop x).1 = (x.val : ZMod a) := by
      simpa only [ZMod.natCast_zmod_val] using
        (coprime_zmod_chineseRemainder_nat_coordinates a b x.val hcop).1
    calc
      (ZMod.chineseRemainder hcop x).1.val =
          (x.val : ZMod a).val := congrArg ZMod.val heq
      _ = x.val % a := ZMod.val_natCast a x.val
  have hcoord_b (x : ZMod (a * b)) :
      (ZMod.chineseRemainder hcop x).2.val = x.val % b := by
    have heq :
        (ZMod.chineseRemainder hcop x).2 = (x.val : ZMod b) := by
      simpa only [ZMod.natCast_zmod_val] using
        (coprime_zmod_chineseRemainder_nat_coordinates a b x.val hcop).2
    calc
      (ZMod.chineseRemainder hcop x).2.val =
          (x.val : ZMod b).val := congrArg ZMod.val heq
      _ = x.val % b := ZMod.val_natCast b x.val
  have hsumz : (∑ x : ZMod (a * b), f x.val) = 0 := by
    calc
      (∑ x : ZMod (a * b), f x.val) =
          (∑ x : ZMod (a * b),
            (((((ZMod.chineseRemainder hcop x).1.val : ℕ) : ℝ) /
                  (a : ℝ)) -
              (((a - 1 : ℕ) : ℝ) / (2 * (a : ℝ)))) *
            (((((ZMod.chineseRemainder hcop x).2.val : ℕ) : ℝ) /
                  (b : ℝ)) -
              (((b - 1 : ℕ) : ℝ) / (2 * (b : ℝ))))) := by
            apply Finset.sum_congr rfl
            intro x hx
            dsimp [f]
            rw [hcoord_a x, hcoord_b x]
      _ = 0 := coprime_zmod_centered_residue_product_zero a b ha hcop
  rw [sum_zmod_val_eq_sum_range (a * b) habpos f] at hsumz
  simpa only [f] using hsumz

/-- The exact gcd covariance identity for *every* positive coprime
pair, on *every* positive common averaging period. It follows from
CRT factorization and the zero mean of the centered residues. -/
theorem empiricalModularCovariance_gcd_coprime
    (a b T : ℕ) (ha : 0 < a) (hb : 0 < b) (hTpos : 0 < T)
    (hcop : a.Coprime b) (haT : a ∣ T) (hbT : b ∣ T) :
    empiricalModularCovariance a b T =
      (((Nat.gcd a b : ℝ) ^ 2 - 1) /
        (12 * (a : ℝ) * (b : ℝ))) := by
  have habpos : 0 < a * b := Nat.mul_pos ha hb
  have ha_ab : a ∣ a * b := ⟨b, rfl⟩
  have hb_ab : b ∣ a * b := ⟨a, by omega⟩
  have hcov :
      empiricalModularCovariance a b T =
        empiricalModularCovariance a b (a * b) := by
    calc
      empiricalModularCovariance a b T =
          empiricalModularCovariance a b (Nat.lcm a b) :=
            empiricalModularCovariance_eq_lcm a b T
              ha hb hTpos haT hbT
      _ = empiricalModularCovariance a b (a * b) :=
            (empiricalModularCovariance_eq_lcm a b (a * b)
              ha hb habpos ha_ab hb_ab).symm
  have hbase : empiricalModularCovariance a b (a * b) = 0 := by
    rw [empiricalModularCovariance_common_period_explicit
      a b (a * b) ha hb habpos ha_ab hb_ab]
    rw [coprime_centered_modular_sum_zero a b ha hb hcop]
    simp
  have hgcd : Nat.gcd a b = 1 := hcop
  rw [hcov, hbase, hgcd]
  norm_num

/-! ## Boundary cases for the full gcd covariance identity -/

/-- The centered fractional part for modulus one vanishes identically. -/
theorem centeredModularFraction_one (m H : ℕ) :
    centeredModularFraction m 1 H = 0 := by
  simp [centeredModularFraction, modularFractionMean, Nat.mod_one]

/-- The covariance with the constant modulus-one residue is zero. -/
theorem empiricalModularCovariance_one_left (b H : ℕ) :
    empiricalModularCovariance 1 b H = 0 := by
  simp [empiricalModularCovariance, centeredModularFraction_one]

theorem empiricalModularCovariance_one_right (a H : ℕ) :
    empiricalModularCovariance a 1 H = 0 := by
  rw [empiricalModularCovariance_comm]
  exact empiricalModularCovariance_one_left a H

/-- The desired gcd formula holds whenever the first modulus is one.
No common-period hypothesis is needed for this boundary case. -/
theorem empiricalModularCovariance_gcd_one_left (b H : ℕ) :
    empiricalModularCovariance 1 b H =
      (((Nat.gcd 1 b : ℝ) ^ 2 - 1) /
        (12 * (1 : ℝ) * (b : ℝ))) := by
  simp [empiricalModularCovariance_one_left]

end TruncatedSieveFlux
