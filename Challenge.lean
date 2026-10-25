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
  ∑ n in Finset.range (Nat.ceil x),
    ∑ d in admittedDivisors K A k n, μ d

/-- Signed mass from the omitted divisors. -/
noncomputable def omittedMass
    (K : ℕ → ℝ) (A : ℝ) (k : ℕ) (x : ℝ) (μ : ℕ → ℝ) : ℝ :=
  ∑ n in Finset.range (Nat.ceil x),
    ∑ d in omittedDivisors K A k n, μ d

/-- Number of omitted divisor incidences, counted with multiplicity in `n`. -/
noncomputable def omittedCount
    (K : ℕ → ℝ) (A : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ∑ n in Finset.range (Nat.ceil x),
    ((omittedDivisors K A k n).card : ℝ)

/-- Absolute value of the admitted signed mass. -/
noncomputable def density
    (K : ℕ → ℝ) (A : ℝ) (k : ℕ) (x : ℝ) (μ : ℕ → ℝ) : ℝ :=
  |admittedMass K A k x μ|

/--
Exact residual identity for any cutoff, not necessarily empty or complete.
All cancellations are consequences of the classical Möbius divisor identity.
-/
theorem moebius_residual_identity
    (K : ℕ → ℝ) (A : ℝ) (k : ℕ) (x : ℝ) (hx : 2 ≤ x) :
    density K A k x moebiusReal =
      |1 - omittedMass K A k x moebiusReal| := by
  sorry

/--
An unconditional combinatorial upper bound for every truncated sieve.
This does NOT assert any uniform asymptotic estimate for an arbitrary cutoff.
-/
theorem moebius_density_le_omitted_count
    (K : ℕ → ℝ) (A : ℝ) (k : ℕ) (x : ℝ) (hx : 2 ≤ x) :
    density K A k x moebiusReal ≤
      1 + omittedCount K A k x := by
  sorry

end TruncatedSieveFlux