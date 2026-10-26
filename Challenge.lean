module

public import Mathlib

public section

namespace TruncatedSieveFlux

/-!
# Truncated divisor sieve

A real-valued finite divisor sieve, with an upper cutoff depending on an
integer index. This Challenge states the finite logarithmic-cutoff residual approximation.

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

/-! ## Quantitative logarithmic-cutoff approximation -/

/-- The finite harmonic sum of Möbius coefficients up to an integer cutoff. -/
noncomputable def harmonicMoebiusMass (B : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 B, moebiusReal d / (d : ℝ)

/-- An elementary finite approximation for the omitted Möbius mass with
A = 0 and K(k) = k, choosing k(x) = 1 + ceil((log x)^4). -/
theorem moebius_log_cutoff_residual_approximation
    (x : ℝ) (hx : 2 ≤ x) :
    |omittedMass (fun j : ℕ => (j : ℝ)) 0 (sieveIndex x) x moebiusReal
      - 1 + ((Nat.ceil x - 1 : ℕ) : ℝ) *
        harmonicMoebiusMass (sieveIndex x)| ≤ (sieveIndex x : ℝ) := by
  sorry

end TruncatedSieveFlux