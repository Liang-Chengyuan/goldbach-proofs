import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Basic.Real.Basic

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_type2_corner_moebius_truncation :
    let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ)
    ∀ (a U : ℕ), 1 < a →
      (∑ d ∈ (Nat.divisors a).filter (fun d => U < d), μ d) =
      - ∑ d ∈ (Nat.divisors a).filter (fun d => d ≤ U), μ d := by
  dsimp only
  intro a U ha
  have h := congrArg (fun f : ArithmeticFunction ℝ => f a)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  have hz : ∑ d ∈ a.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) = 0 := by
    simpa [ArithmeticFunction.one_apply, ne_of_gt ha] using h
  apply eq_neg_of_add_eq_zero_left
  rw [← hz]
  simpa only [not_lt] using
    Finset.sum_filter_add_sum_filter_not a.divisors (fun d => U < d)
      (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ))
