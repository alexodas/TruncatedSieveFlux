module

public import Mathlib

public section

namespace TruncatedSieveFlux

/-!
# Truncated divisor sieve

A real-valued finite divisor sieve, with an upper cutoff depending on an
integer index. The stated results concern an exact residual identity and a
combinatorial estimate for classical Möbius coefficients.

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

/-- Number of omitted divisor incidences, counted with multiplicity in `n`. -/
noncomputable def omittedCount
    (K : ℕ → ℝ) (A : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (Nat.ceil x),
    ((omittedDivisors K A k n).card : ℝ)

/-- Absolute value of the admitted signed mass. -/
noncomputable def density
    (K : ℕ → ℝ) (A : ℝ) (k : ℕ) (x : ℝ) (μ : ℕ → ℝ) : ℝ :=
  |admittedMass K A k x μ|

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

/-- Main residual identity. -/
theorem moebius_residual_identity
    (K : ℕ → ℝ) (A : ℝ) (k : ℕ) (x : ℝ) (hx : 2 ≤ x) :
    density K A k x moebiusReal =
      |1 - omittedMass K A k x moebiusReal| := by
  have h := admitted_add_omitted K A k x moebiusReal
  rw [complete_moebius_mass x hx] at h
  change |admittedMass K A k x moebiusReal| =
    |1 - omittedMass K A k x moebiusReal|
  congr 1
  linarith

private theorem abs_moebiusReal_le_one (d : ℕ) :
    |moebiusReal d| ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or d with h | h | h
  · simp [moebiusReal, h]
  · simp [moebiusReal, h]
  · simp [moebiusReal, h]

private theorem abs_omittedMass_le_count
    (K : ℕ → ℝ) (A : ℝ) (k : ℕ) (x : ℝ) :
    |omittedMass K A k x moebiusReal| ≤ omittedCount K A k x := by
  unfold omittedMass omittedCount
  calc
    |∑ n ∈ Finset.range (Nat.ceil x),
      ∑ d ∈ omittedDivisors K A k n, moebiusReal d| ≤
        ∑ n ∈ Finset.range (Nat.ceil x),
          |∑ d ∈ omittedDivisors K A k n, moebiusReal d| :=
            Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range (Nat.ceil x),
          ∑ d ∈ omittedDivisors K A k n, |moebiusReal d| := by
        apply Finset.sum_le_sum
        intro n hn
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range (Nat.ceil x),
          ∑ d ∈ omittedDivisors K A k n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        apply Finset.sum_le_sum
        intro d hd
        exact abs_moebiusReal_le_one d
    _ = ∑ n ∈ Finset.range (Nat.ceil x),
          ((omittedDivisors K A k n).card : ℝ) := by simp

/-- Quantitative upper bound by omitted divisor incidences. -/
theorem moebius_density_le_omitted_count
    (K : ℕ → ℝ) (A : ℝ) (k : ℕ) (x : ℝ) (hx : 2 ≤ x) :
    density K A k x moebiusReal ≤
      1 + omittedCount K A k x := by
  calc
    density K A k x moebiusReal =
        |1 - omittedMass K A k x moebiusReal| :=
          moebius_residual_identity K A k x hx
    _ ≤ 1 + |omittedMass K A k x moebiusReal| := by
        have h := abs_add_le (1 : ℝ)
          (-omittedMass K A k x moebiusReal)
        simpa only [sub_eq_add_neg, abs_one, abs_neg] using h
    _ ≤ 1 + omittedCount K A k x := by
        exact add_le_add_right (abs_omittedMass_le_count K A k x) 1

end TruncatedSieveFlux