import Mathlib

theorem PEqualNP.Outside.L_goldbach_moving_weights_linear_taper :
    ∀ n : ℕ, 0<n → (∑ k ∈ Finset.range n,(1-(k:ℝ)/n))=((n:ℝ)+1)/2 := by
  intro n hn
  have key : ∀ m : ℕ, (∑ k ∈ Finset.range m, (k:ℝ)) = (m:ℝ) * ((m:ℝ) - 1) / 2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have hsplit : (∑ k ∈ Finset.range n, (1 - (k:ℝ)/n))
      = (n:ℝ) - (∑ k ∈ Finset.range n, (k:ℝ)) / (n:ℝ) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, key n]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [hsplit, key n]
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  field_simp
  ring
