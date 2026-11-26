import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

open Finset

private theorem prefix_term (k : ℕ) (hk : k < 8000000000) :
    ArithmeticFunction.vonMangoldt k ≤ 33 := by
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · simp
  have hpow : (k : ℝ) ≤ (2 : ℝ)^33 := by
    exact_mod_cast (show k ≤ 2^33 by omega)
  have hlog := Real.log_le_log (Nat.cast_pos.mpr hpos) hpow
  rw [Real.log_pow] at hlog
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  apply (ArithmeticFunction.vonMangoldt_le_log (n := k)).trans
  norm_num at hlog htwo
  linarith only [hlog, htwo]

private theorem prefix_error (q a m : ℕ) (hq : 0 < q) (hm : m < 8000000000) :
    |(∑ k ∈ (range (m+1)).filter (fun k => k % q = a % q),
        ArithmeticFunction.vonMangoldt k) - (m:ℝ)/q.totient| ≤ 264000000000 := by
  let s := (range (m+1)).filter (fun k => k % q = a % q)
  have hcard : s.card ≤ 8000000000 := by
    have h := card_le_card (filter_subset (fun k => k % q = a % q) (range (m+1)))
    simpa only [card_range] using h.trans (by simpa only [card_range] using Nat.succ_le_of_lt hm)
  have upper : (∑ k ∈ s, ArithmeticFunction.vonMangoldt k) ≤ ∑ _k ∈ s, (33:ℝ) := by
    apply sum_le_sum
    intro k hk
    have hkm := mem_range.mp (mem_filter.mp hk).1
    exact prefix_term k (by omega)
  have lower : 0 ≤ ∑ k ∈ s, ArithmeticFunction.vonMangoldt k :=
    sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
  have hp : (1:ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hmain : (m:ℝ)/q.totient ≤ (m:ℝ) := div_le_self (by positivity) hp
  have hmn : (m:ℝ) ≤ 8000000000 := by exact_mod_cast hm.le
  have hcn : (s.card:ℝ) ≤ 8000000000 := by exact_mod_cast hcard
  have hnon : 0 ≤ (m:ℝ)/q.totient := by positivity
  change |(∑ k ∈ s, ArithmeticFunction.vonMangoldt k) - (m:ℝ)/q.totient| ≤ _
  rw [abs_le]
  simp only [sum_const, nsmul_eq_mul] at upper
  constructor <;> linarith

theorem PEqualNP.Outside.L_goldbach_finite_phase_early_prefix_cost :
    let D := fun (q a n : ℕ) => (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k) - (n:ℝ)/(Nat.totient q:ℝ); let J := fun (q a l u : ℕ) (β : ℝ) => 2 * Real.pi * |β| * (∑ m ∈ Finset.Ico l u, |D q a m|); let T : ℕ := 8000000000; ∀ (q a n : ℕ) (β : ℝ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q → 4000000000000000000 ≤ n → |β| ≤ 105/((q:ℝ)*n) → J q a 0 T β ≤ (n:ℝ)/10^12 := by
  dsimp only
  intro q a n β hq _ _ _ hn hβ
  have S := sum_le_sum (s := Ico 0 8000000000)
    (g := fun _ : ℕ => (264000000000:ℝ))
    (fun m hm => prefix_error q a m (by omega) (mem_Ico.mp hm).2)
  simp only [sum_const, Nat.card_Ico, Nat.sub_zero, nsmul_eq_mul] at S
  have qlo : (3:ℝ) ≤ q := by exact_mod_cast hq
  have nlo : (4000000000000000000:ℝ) ≤ n := by exact_mod_cast hn
  have hlo : (3:ℝ)*4000000000000000000 ≤ (q:ℝ)*n := by gcongr
  have B : |β| ≤ 105/((3:ℝ)*4000000000000000000) :=
    hβ.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlo)
  calc
    _ ≤ 2 * (4:ℝ) * (105 / (3 * 4000000000000000000)) *
        (8000000000 * 264000000000) := by
          gcongr
          · exact Real.pi_lt_four.le
          · exact_mod_cast S
    _ ≤ (4000000000000000000:ℝ) / 10^12 := by norm_num
    _ ≤ _ := by gcongr
