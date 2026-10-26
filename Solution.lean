module

public import Mathlib

public section

namespace TruncatedSieveFlux

/-!
# Truncated divisor sieve

A real-valued finite divisor sieve, with an upper cutoff depending on an
integer index. This module retains the quantitative finite approximation of the
omitted Möbius mass, with private supporting divisor identities.

No unqualified analytic asymptotic estimate is asserted.
-/

/-- A dynamic index (the concrete growth law can be changed independently). -/
noncomputable def sieveIndex (x : ℝ) : ℕ :=
  1 + Nat.ceil ((Real.log x) ^ 4)

/-- The classical integer-valued Möbius function embedded in the reals. -/
noncomputable def moebiusReal (d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ)

/-- Divisors admitted by the cutoff interval `(A, K k]`. -/
noncomputable def admittedDivisors
    (K : ℕ → ℝ) (A : ℝ) (k n : ℕ) : Finset ℕ := by
  classical
  exact (Nat.divisors n).filter
    (fun d => A < (d : ℝ) ∧ (d : ℝ) ≤ K k)

/-- Divisors not admitted by the cutoff interval. -/
noncomputable def omittedDivisors
    (K : ℕ → ℝ) (A : ℝ) (k n : ℕ) : Finset ℕ := by
  classical
  exact (Nat.divisors n).filter
    (fun d => ¬ (A < (d : ℝ) ∧ (d : ℝ) ≤ K k))

/-- Signed mass from the admitted divisors. -/
noncomputable def admittedMass
    (K : ℕ → ℝ) (A : ℝ) (k : ℕ) (x : ℝ) (μ : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.range (Nat.ceil x),
    ∑ d ∈ admittedDivisors K A k n, μ d

/-- Signed mass from the omitted divisors. -/
noncomputable def omittedMass
    (K : ℕ → ℝ) (A : ℝ) (k : ℕ) (x : ℝ) (μ : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.range (Nat.ceil x),
    ∑ d ∈ omittedDivisors K A k n, μ d

/-! ## Finite Möbius cancellation and the residual decomposition -/

private theorem moebius_divisor_sum (n : ℕ) :
    (∑ d ∈ Nat.divisors n, moebiusReal d) =
      if n = 1 then 1 else 0 := by
  have h := congrArg
    (fun f : ArithmeticFunction ℤ => f n)
    ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simp only [ArithmeticFunction.one_apply] at h
  change (∑ d ∈ Nat.divisors n,
    ((ArithmeticFunction.moebius d : ℤ) : ℝ)) =
      if n = 1 then 1 else 0
  exact_mod_cast h

private theorem complete_moebius_mass (x : ℝ) (hx : 2 ≤ x) :
    (∑ n ∈ Finset.range (Nat.ceil x),
      ∑ d ∈ Nat.divisors n, moebiusReal d) = 1 := by
  have h1 : (1 : ℕ) ∈ Finset.range (Nat.ceil x) := by
    apply Finset.mem_range.mpr
    have h12 : ((1 : ℕ) : ℝ) < (2 : ℝ) := by norm_num
    exact Nat.lt_ceil.mpr (lt_of_lt_of_le h12 hx)
  calc
    (∑ n ∈ Finset.range (Nat.ceil x),
      ∑ d ∈ Nat.divisors n, moebiusReal d) =
        ∑ n ∈ Finset.range (Nat.ceil x),
          if n = 1 then (1 : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro n hn
            exact moebius_divisor_sum n
    _ = 1 := by simp [Finset.sum_ite_eq', h1]

private theorem admitted_add_omitted
    (K : ℕ → ℝ) (A : ℝ) (k : ℕ) (x : ℝ) (μ : ℕ → ℝ) :
    admittedMass K A k x μ + omittedMass K A k x μ =
      ∑ n ∈ Finset.range (Nat.ceil x),
        ∑ d ∈ Nat.divisors n, μ d := by
  classical
  unfold admittedMass omittedMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  simpa only [admittedDivisors, omittedDivisors] using
    (Finset.sum_filter_add_sum_filter_not (Nat.divisors n)
      (fun d : ℕ => A < (d : ℝ) ∧ (d : ℝ) ≤ K k) μ)

private theorem abs_moebiusReal_le_one (d : ℕ) :
    |moebiusReal d| ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or d with h | h | h
  · simp [moebiusReal, h]
  · simp [moebiusReal, h]
  · simp [moebiusReal, h]

/-! ## Quantitative approximation of the floor-weighted Möbius sum -/

/-- The finite harmonic sum of Möbius coefficients up to an integer cutoff. -/
noncomputable def harmonicMoebiusMass (B : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 B, moebiusReal d / (d : ℝ)

/-- Möbius coefficients weighted by the count of positive multiples at most M. -/
noncomputable def floorWeightedMoebiusMass (M B : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 B, moebiusReal d * ((M / d : ℕ) : ℝ)


/-- The number of positive multiples of d not exceeding M is M / d. -/
private theorem card_multiples_Icc (M d : ℕ) (hd : 0 < d) :
    ((Finset.Icc 1 M).filter (fun n => d ∣ n)).card = M / d := by
  classical
  have hinj : Function.Injective (fun q : ℕ => d * q) := by
    intro a b h
    apply Nat.eq_of_mul_eq_mul_left hd
    exact h
  have hset :
      ((Finset.Icc 1 (M / d)).image (fun q => d * q)) =
        (Finset.Icc 1 M).filter (fun n => d ∣ n) := by
    ext n
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨q, ⟨hqpos, hqle⟩, rfl⟩
      have hbound : (M / d) * d ≤ M := Nat.div_mul_le_self M d
      refine ⟨⟨by nlinarith, ?_⟩, ?_⟩
      · nlinarith
      · exact dvd_mul_right d q
    · rintro ⟨⟨hnpos, hnle⟩, hdn⟩
      rcases hdn with ⟨q, hq⟩
      refine ⟨q, ⟨?_, ?_⟩, hq.symm⟩
      · by_contra h
        have h0 : q = 0 := by omega
        simp [h0] at hq
        omega
      · apply (Nat.le_div_iff_mul_le hd).2
        nlinarith
  calc
    ((Finset.Icc 1 M).filter (fun n => d ∣ n)).card =
      ((Finset.Icc 1 (M / d)).image (fun q => d * q)).card := by rw [hset]
    _ = (Finset.Icc 1 (M / d)).card := Finset.card_image_of_injective _ hinj
    _ = M / d := by simp

/-- A fully finite error bound for replacing integer quotients by real quotients. -/
theorem moebius_floor_rounding_error_le (M B : ℕ) :
    |floorWeightedMoebiusMass M B -
      (M : ℝ) * harmonicMoebiusMass B| ≤ (B : ℝ) := by
  classical
  have hterm (d : ℕ) (hd : d ∈ Finset.Icc 1 B) :
      |moebiusReal d * ((M / d : ℕ) : ℝ) -
          (M : ℝ) * (moebiusReal d / (d : ℝ))| ≤ 1 := by
    have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
    have hdposR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
    have hmod : (M : ℝ) =
        ((M % d : ℕ) : ℝ) + (d : ℝ) * ((M / d : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mod_add_div M d).symm
    have hmodLt : ((M % d : ℕ) : ℝ) < (d : ℝ) := by
      exact_mod_cast Nat.mod_lt M hdpos
    have hmodNonneg : (0 : ℝ) ≤ ((M % d : ℕ) : ℝ) := by positivity
    have hlow : ((M / d : ℕ) : ℝ) ≤ (M : ℝ) / (d : ℝ) := by
      apply (le_div_iff₀ hdposR).2
      nlinarith
    have hupp : (M : ℝ) / (d : ℝ) ≤ ((M / d : ℕ) : ℝ) + 1 := by
      apply (div_le_iff₀ hdposR).2
      nlinarith
    have hround :
        |((M / d : ℕ) : ℝ) - (M : ℝ) / (d : ℝ)| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> linarith
    have hrewrite :
        moebiusReal d * ((M / d : ℕ) : ℝ) -
            (M : ℝ) * (moebiusReal d / (d : ℝ)) =
          moebiusReal d * (((M / d : ℕ) : ℝ) - (M : ℝ) / (d : ℝ)) := by
      ring
    rw [hrewrite, abs_mul]
    calc
      |moebiusReal d| * |((M / d : ℕ) : ℝ) - (M : ℝ) / (d : ℝ)| ≤
        1 * 1 := mul_le_mul (abs_moebiusReal_le_one d) hround
          (abs_nonneg _) (by norm_num)
      _ = 1 := by ring
  unfold floorWeightedMoebiusMass harmonicMoebiusMass
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    |∑ d ∈ Finset.Icc 1 B,
      (moebiusReal d * ((M / d : ℕ) : ℝ) -
          (M : ℝ) * (moebiusReal d / (d : ℝ)))| ≤
        ∑ d ∈ Finset.Icc 1 B,
          |moebiusReal d * ((M / d : ℕ) : ℝ) -
            (M : ℝ) * (moebiusReal d / (d : ℝ))| :=
              Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 B, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact hterm d hd
    _ = (B : ℝ) := by simp


/-- With A = 0 and integer upper cutoff B, regrouping the finite divisor
sum gives the sum of Möbius coefficients weighted by integer quotients. -/
private theorem admittedMass_integer_cutoff_eq_floor
    (B : ℕ) (x : ℝ) (hx : 2 ≤ x) :
    admittedMass (fun j : ℕ => (j : ℝ)) 0 B x moebiusReal =
      floorWeightedMoebiusMass (Nat.ceil x - 1) B := by
  classical
  let M : ℕ := Nat.ceil x - 1
  have hceil : M + 1 = Nat.ceil x := by
    have h02 : ((0 : ℕ) : ℝ) < (2 : ℝ) := by norm_num
    have hn : 0 < Nat.ceil x :=
      Nat.lt_ceil.mpr (lt_of_lt_of_le h02 hx)
    dsimp [M]
    omega
  have hinner (n : ℕ) :
      (∑ d ∈ admittedDivisors (fun j : ℕ => (j : ℝ)) 0 B n,
        moebiusReal d) =
        ∑ d ∈ Finset.Icc 1 B,
          if d ∣ n ∧ n ≠ 0 then moebiusReal d else 0 := by
    have hset :
        admittedDivisors (fun j : ℕ => (j : ℝ)) 0 B n =
          (Finset.Icc 1 B).filter (fun d => d ∣ n ∧ n ≠ 0) := by
      ext d
      constructor
      · intro hd
        have hd' : d ∈ Nat.divisors n ∧
            (0 : ℝ) < (d : ℝ) ∧ (d : ℝ) ≤ (B : ℝ) := by
          simpa only [admittedDivisors, Finset.mem_filter] using hd
        obtain ⟨hdvd, hd0, hdB⟩ := hd'
        obtain ⟨hdiv, hn⟩ := Nat.mem_divisors.mp hdvd
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ⟨hdiv, hn⟩⟩
        · exact_mod_cast hd0
        · exact_mod_cast hdB
      · intro hd
        obtain ⟨hdi, hdiv, hn⟩ := Finset.mem_filter.mp hd
        obtain ⟨hd0, hdB⟩ := Finset.mem_Icc.mp hdi
        have hNat : d ∈ Nat.divisors n :=
          Nat.mem_divisors.mpr ⟨hdiv, hn⟩
        show d ∈ admittedDivisors (fun j : ℕ => (j : ℝ)) 0 B n
        simp only [admittedDivisors, Finset.mem_filter]
        exact ⟨hNat, ⟨by exact_mod_cast hd0, by exact_mod_cast hdB⟩⟩
    rw [hset, Finset.sum_filter]
  have hcount (d : ℕ) (hd : d ∈ Finset.Icc 1 B) :
      ((Finset.range (Nat.ceil x)).filter (fun n => d ∣ n ∧ n ≠ 0)).card =
        M / d := by
    have hset :
        (Finset.range (Nat.ceil x)).filter (fun n => d ∣ n ∧ n ≠ 0) =
          (Finset.Icc 1 M).filter (fun n => d ∣ n) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      constructor
      · rintro ⟨hnlt, hdvd, hnne⟩
        exact ⟨⟨by omega, by omega⟩, hdvd⟩
      · rintro ⟨⟨hnpos, hnM⟩, hdvd⟩
        exact ⟨by omega, hdvd, by omega⟩
    rw [hset]
    exact card_multiples_Icc M d (Finset.mem_Icc.mp hd).1
  unfold admittedMass floorWeightedMoebiusMass
  calc
    (∑ n ∈ Finset.range (Nat.ceil x),
      ∑ d ∈ admittedDivisors (fun j : ℕ => (j : ℝ)) 0 B n,
        moebiusReal d) =
        ∑ n ∈ Finset.range (Nat.ceil x),
          ∑ d ∈ Finset.Icc 1 B,
            if d ∣ n ∧ n ≠ 0 then moebiusReal d else 0 := by
          apply Finset.sum_congr rfl
          intro n hn
          exact hinner n
    _ = ∑ d ∈ Finset.Icc 1 B,
          ∑ n ∈ Finset.range (Nat.ceil x),
            if d ∣ n ∧ n ≠ 0 then moebiusReal d else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.Icc 1 B,
          moebiusReal d *
            (((Finset.range (Nat.ceil x)).filter
              (fun n => d ∣ n ∧ n ≠ 0)).card : ℝ) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [← Finset.sum_filter]
          simp [mul_comm]
    _ = ∑ d ∈ Finset.Icc 1 B,
          moebiusReal d * ((M / d : ℕ) : ℝ) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [hcount d hd]

/-- Logarithmic-cutoff quantitative approximation for the omitted Möbius
mass. Unlike an asymptotic bound, this is a fully finite inequality. -/
theorem moebius_log_cutoff_residual_approximation
    (x : ℝ) (hx : 2 ≤ x) :
    |omittedMass (fun j : ℕ => (j : ℝ)) 0 (sieveIndex x) x moebiusReal
      - 1 + ((Nat.ceil x - 1 : ℕ) : ℝ) *
        harmonicMoebiusMass (sieveIndex x)| ≤ (sieveIndex x : ℝ) := by
  let B := sieveIndex x
  have hsum :=
    admitted_add_omitted (fun j : ℕ => (j : ℝ)) 0 B x moebiusReal
  rw [complete_moebius_mass x hx] at hsum
  have hfloor := admittedMass_integer_cutoff_eq_floor B x hx
  have hr :
      omittedMass (fun j : ℕ => (j : ℝ)) 0 B x moebiusReal =
        1 - floorWeightedMoebiusMass (Nat.ceil x - 1) B := by
    linarith
  change
    |omittedMass (fun j : ℕ => (j : ℝ)) 0 B x moebiusReal
       - 1 + ((Nat.ceil x - 1 : ℕ) : ℝ) *
         harmonicMoebiusMass B| ≤ (B : ℝ)
  calc
    |omittedMass (fun j : ℕ => (j : ℝ)) 0 B x moebiusReal
       - 1 + ((Nat.ceil x - 1 : ℕ) : ℝ) * harmonicMoebiusMass B| =
        |-(floorWeightedMoebiusMass (Nat.ceil x - 1) B -
          ((Nat.ceil x - 1 : ℕ) : ℝ) * harmonicMoebiusMass B)| := by
          rw [hr]
          congr 1
          ring
    _ = |floorWeightedMoebiusMass (Nat.ceil x - 1) B -
        ((Nat.ceil x - 1 : ℕ) : ℝ) * harmonicMoebiusMass B| := abs_neg _
    _ ≤ (B : ℝ) := moebius_floor_rounding_error_le _ _


/-- Exact modulo representation for the finite rounding discrepancy. -/
theorem harmonic_floor_discrepancy_eq_mod_sum (M B : ℕ) :
    (M : ℝ) * harmonicMoebiusMass B - floorWeightedMoebiusMass M B =
      ∑ d ∈ Finset.Icc 1 B,
        moebiusReal d * (((M % d : ℕ) : ℝ) / (d : ℝ)) := by
  classical
  have hterm (d : ℕ) (hd : d ∈ Finset.Icc 1 B) :
      (M : ℝ) * (moebiusReal d / (d : ℝ)) -
          moebiusReal d * ((M / d : ℕ) : ℝ) =
        moebiusReal d * (((M % d : ℕ) : ℝ) / (d : ℝ)) := by
    have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
    have hne : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hdpos)
    have hmod : (M : ℝ) =
        ((M % d : ℕ) : ℝ) + (d : ℝ) * ((M / d : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mod_add_div M d).symm
    have hfrac :
        (M : ℝ) / (d : ℝ) - ((M / d : ℕ) : ℝ) =
          ((M % d : ℕ) : ℝ) / (d : ℝ) := by
      apply (eq_div_iff hne).2
      field_simp [hne]
      nlinarith [hmod]
    calc
      (M : ℝ) * (moebiusReal d / (d : ℝ)) -
          moebiusReal d * ((M / d : ℕ) : ℝ) =
          moebiusReal d *
            ((M : ℝ) / (d : ℝ) - ((M / d : ℕ) : ℝ)) := by ring
      _ = moebiusReal d *
          (((M % d : ℕ) : ℝ) / (d : ℝ)) := by rw [hfrac]
  unfold harmonicMoebiusMass floorWeightedMoebiusMass
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  exact hterm d hd

end TruncatedSieveFlux