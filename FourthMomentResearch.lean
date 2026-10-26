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
