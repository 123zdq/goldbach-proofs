import Mathlib

open scoped BigOperators

namespace Conjectures.Goldbach.DyadicCellWindowTransfer_aux

/-- Block transfer for a nonnegative weight `w` on `[4m, 5m)`, split into `B` blocks of length `H`
(`B * H = m`). If every window of length `H` starting in `[8m/3, 16m/3]` carries weight at least
`H / 2`, then the within-block difference quotient plus `m / 4` is at most the reflected pairing
sum over `[8m/3, 16m/3]`. -/
theorem blockTransfer (w : ℕ → ℝ) (hw : ∀ q, 0 ≤ w q) (m H B : ℕ) (hH : 0 < H)
    (hB : 0 < B) (hBH : B * H = m) (hmid : w (4 * m) = 0)
    (hyp : ∀ x : ℕ, 8 * m ≤ 3 * x → 3 * x ≤ 2 * (8 * m) →
      (H : ℝ) / 2 ≤ ∑ t ∈ Finset.range H, w (x + t)) :
    ((8 * m : ℕ) : ℝ) / 32 +
      (∑ j ∈ Finset.range B, (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
        (w (8 * m / 2 + j * H + s) - w (8 * m / 2 + j * H + t)) *
          (w (8 * m - (8 * m / 2 + j * H + s)) - w (8 * m - (8 * m / 2 + j * H + t)))) /
            (2 * (H : ℝ))) ≤
      ∑ q ∈ (Finset.range (8 * m + 1)).filter (fun q => 8 * m ≤ 3 * q ∧ 3 * q ≤ 2 * (8 * m)),
        w q * w (8 * m - q) := by
  have hm0 : 0 < m := by rw [← hBH]; exact Nat.mul_pos hB hH
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hHne : (H : ℝ) ≠ 0 := ne_of_gt hHr
  rw [show 8 * m / 2 = 4 * m from by omega]
  -- every block stays below `m`
  have key : ∀ j ∈ Finset.range B, j * H + H ≤ m := by
    intro j hj
    have h1 : (j + 1) * H ≤ B * H := Nat.mul_le_mul_right H (by simp at hj; omega)
    rw [add_mul, one_mul, hBH] at h1
    omega
  obtain ⟨A, hA⟩ : ∃ A : ℕ → ℝ, ∀ j, A j = ∑ t ∈ Finset.range H, w (4 * m + j * H + t) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ, ∀ j, D j = ∑ t ∈ Finset.range H, w (8 * m - (4 * m + j * H + t)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℕ → ℝ,
      ∀ j, C j = ∑ t ∈ Finset.range H, w (4 * m + j * H + t) * w (8 * m - (4 * m + j * H + t)) :=
    ⟨_, fun _ => rfl⟩
  -- forward block mass
  have hA2 : ∀ j ∈ Finset.range B, (H : ℝ) / 2 ≤ A j := by
    intro j hj
    rw [hA]
    exact hyp (4 * m + j * H) (by omega) (by have := key j hj; omega)
  -- reflected block mass
  have hD2 : ∀ j ∈ Finset.range B, (H : ℝ) / 2 ≤ D j := by
    intro j hj
    have hkey := key j hj
    rw [hD]
    have hre : (∑ t ∈ Finset.range H, w (8 * m - (4 * m + j * H + t)))
        = ∑ t ∈ Finset.range H, w (4 * m - (j * H + H) + 1 + t) := by
      calc (∑ t ∈ Finset.range H, w (8 * m - (4 * m + j * H + t)))
          = ∑ t ∈ Finset.range H, w (4 * m - (j * H + H) + 1 + (H - 1 - t)) := by
            refine Finset.sum_congr rfl (fun t ht => ?_)
            have htH : t < H := Finset.mem_range.mp ht
            rw [show 8 * m - (4 * m + j * H + t) = 4 * m - (j * H + H) + 1 + (H - 1 - t) from by
              omega]
        _ = ∑ t ∈ Finset.range H, w (4 * m - (j * H + H) + 1 + t) :=
          Finset.sum_range_reflect (fun i => w (4 * m - (j * H + H) + 1 + i)) H
    rw [hre]
    exact hyp (4 * m - (j * H + H) + 1) (by omega) (by omega)
  -- the within-block difference expands into the diagonal and the product of block masses
  have ident : ∀ j ∈ Finset.range B, (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
        (w (4 * m + j * H + s) - w (4 * m + j * H + t)) *
          (w (8 * m - (4 * m + j * H + s)) - w (8 * m - (4 * m + j * H + t))))
      = 2 * ((H : ℝ) * C j - A j * D j) := by
    intro j _
    have hexp : ∀ s t : ℕ,
        (w (4 * m + j * H + s) - w (4 * m + j * H + t)) *
            (w (8 * m - (4 * m + j * H + s)) - w (8 * m - (4 * m + j * H + t)))
        = w (4 * m + j * H + s) * w (8 * m - (4 * m + j * H + s))
          - w (4 * m + j * H + s) * w (8 * m - (4 * m + j * H + t))
          - w (4 * m + j * H + t) * w (8 * m - (4 * m + j * H + s))
          + w (4 * m + j * H + t) * w (8 * m - (4 * m + j * H + t)) := fun s t => by ring
    have h1 : (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
          w (4 * m + j * H + s) * w (8 * m - (4 * m + j * H + s))) = (H : ℝ) * C j := by
      have hinner : ∀ s : ℕ, (∑ t ∈ Finset.range H,
          w (4 * m + j * H + s) * w (8 * m - (4 * m + j * H + s)))
          = (H : ℝ) * (w (4 * m + j * H + s) * w (8 * m - (4 * m + j * H + s))) := by
        intro s
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      simp only [hinner]
      rw [← Finset.mul_sum, hC]
    have h2 : (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
          w (4 * m + j * H + s) * w (8 * m - (4 * m + j * H + t))) = A j * D j := by
      rw [hA, hD]
      exact (Finset.sum_mul_sum _ _ _ _).symm
    have h3 : (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
          w (4 * m + j * H + t) * w (8 * m - (4 * m + j * H + s))) = A j * D j := by
      rw [Finset.sum_comm, hA, hD]
      exact (Finset.sum_mul_sum _ _ _ _).symm
    have h4 : (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
          w (4 * m + j * H + t) * w (8 * m - (4 * m + j * H + t))) = (H : ℝ) * C j := by
      rw [Finset.sum_comm]
      have hinner : ∀ t : ℕ, (∑ s ∈ Finset.range H,
          w (4 * m + j * H + t) * w (8 * m - (4 * m + j * H + t)))
          = (H : ℝ) * (w (4 * m + j * H + t) * w (8 * m - (4 * m + j * H + t))) := by
        intro t
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      simp only [hinner]
      rw [← Finset.mul_sum, hC]
    simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2, h3, h4]
    ring
  -- the block indices enumerate an interval
  have hsplit : (∑ j ∈ Finset.range B, ∑ t ∈ Finset.range H,
        w (4 * m + j * H + t) * w (8 * m - (4 * m + j * H + t)))
      = ∑ u ∈ Finset.range (B * H), w (4 * m + u) * w (8 * m - (4 * m + u)) := by
    calc (∑ j ∈ Finset.range B, ∑ t ∈ Finset.range H,
          w (4 * m + j * H + t) * w (8 * m - (4 * m + j * H + t)))
        = ∑ x ∈ Finset.range B ×ˢ Finset.range H,
            w (4 * m + x.1 * H + x.2) * w (8 * m - (4 * m + x.1 * H + x.2)) :=
          (Finset.sum_product (Finset.range B) (Finset.range H)
            (fun x : ℕ × ℕ =>
              w (4 * m + x.1 * H + x.2) * w (8 * m - (4 * m + x.1 * H + x.2)))).symm
      _ = ∑ u ∈ Finset.range (B * H), w (4 * m + u) * w (8 * m - (4 * m + u)) := by
        refine Finset.sum_nbij' (fun x : ℕ × ℕ => x.1 * H + x.2) (fun u => (u / H, u % H))
          ?_ ?_ ?_ ?_ (fun x _ => by simp only [Nat.add_assoc])
        · intro x hx
          simp only [Finset.mem_product, Finset.mem_range] at hx
          have h1 : (x.1 + 1) * H ≤ B * H := Nat.mul_le_mul_right H (by omega)
          rw [add_mul, one_mul] at h1
          simp only [Finset.mem_range]
          omega
        · intro u hu
          simp only [Finset.mem_product, Finset.mem_range] at hu ⊢
          have h1 : u / H * H + u % H = u := by
            rw [Nat.mul_comm]
            exact Nat.div_add_mod u H
          have h2 : u % H < H := Nat.mod_lt _ hH
          constructor
          · by_contra hcon
            have h3 : B * H ≤ u / H * H := Nat.mul_le_mul_right H (by omega)
            omega
          · exact h2
        · intro x hx
          simp only [Finset.mem_product, Finset.mem_range] at hx
          have hlt : x.2 < H := hx.2
          show ((x.1 * H + x.2) / H, (x.1 * H + x.2) % H) = x
          rw [Nat.mul_comm, Nat.mul_add_div hH, Nat.div_eq_of_lt hlt, Nat.add_zero,
            Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
        · intro u _
          show u / H * H + u % H = u
          rw [Nat.mul_comm]
          exact Nat.div_add_mod u H
  have hCsplit : (∑ j ∈ Finset.range B, C j)
      = ∑ q ∈ Finset.Ico (4 * m) (5 * m), w q * w (8 * m - q) := by
    rw [Finset.sum_Ico_eq_sum_range, show 5 * m - 4 * m = B * H from by omega, ← hsplit]
    exact Finset.sum_congr rfl (fun j _ => hC j)
  -- reflection doubles the pairing sum
  have hRefl : (∑ q ∈ Finset.Ico (4 * m) (5 * m), w q * w (8 * m - q))
        + (∑ q ∈ Finset.Ico (4 * m) (5 * m), w q * w (8 * m - q))
      ≤ ∑ q ∈ (Finset.range (8 * m + 1)).filter (fun q => 8 * m ≤ 3 * q ∧ 3 * q ≤ 2 * (8 * m)),
        w q * w (8 * m - q) := by
    have hQ0 : ∀ q ∈ Finset.Ico (4 * m) (5 * m),
        q ∈ (Finset.range (8 * m + 1)).filter (fun q => 8 * m ≤ 3 * q ∧ 3 * q ≤ 2 * (8 * m)) := by
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hq ⊢
      omega
    have hQ1 : ∀ q ∈ Finset.Ico (4 * m + 1) (5 * m),
        (8 * m - q ∈ (Finset.range (8 * m + 1)).filter
          (fun q => 8 * m ≤ 3 * q ∧ 3 * q ≤ 2 * (8 * m))) ∧
          ∀ r ∈ Finset.Ico (4 * m) (5 * m), r ≠ 8 * m - q := by
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hq ⊢
      refine ⟨?_, fun r hr => ?_⟩ <;> omega
    have hR1 : (∑ q ∈ (Finset.Ico (4 * m + 1) (5 * m)).image (fun q => 8 * m - q),
          w q * w (8 * m - q))
        = ∑ q ∈ Finset.Ico (4 * m) (5 * m), w q * w (8 * m - q) := by
      rw [Finset.sum_image (f := fun q => w q * w (8 * m - q))
        (fun q hq q' hq' h => by simp only [Finset.mem_coe, Finset.mem_Ico] at hq hq'; omega)]
      have htermR : ∀ q ∈ Finset.Ico (4 * m + 1) (5 * m),
          w (8 * m - q) * w (8 * m - (8 * m - q)) = w q * w (8 * m - q) := by
        intro q hq
        simp only [Finset.mem_Ico] at hq
        rw [show 8 * m - (8 * m - q) = q from by omega]
        ring
      rw [Finset.sum_congr rfl htermR,
        show Finset.Ico (4 * m + 1) (5 * m) = (Finset.Ico (4 * m) (5 * m)).erase (4 * m) from by
          ext q
          simp only [Finset.mem_Ico, Finset.mem_erase]
          omega]
      have hz : (fun q => w q * w (8 * m - q)) (4 * m) = 0 := by
        show w (4 * m) * w (8 * m - 4 * m) = 0
        rw [show 8 * m - 4 * m = 4 * m from by omega, hmid]
        ring
      exact Finset.sum_erase _ hz
    calc (∑ q ∈ Finset.Ico (4 * m) (5 * m), w q * w (8 * m - q))
        + (∑ q ∈ Finset.Ico (4 * m) (5 * m), w q * w (8 * m - q))
        = (∑ q ∈ Finset.Ico (4 * m) (5 * m), w q * w (8 * m - q))
          + ∑ q ∈ (Finset.Ico (4 * m + 1) (5 * m)).image (fun q => 8 * m - q),
            w q * w (8 * m - q) := by rw [hR1]
      _ = ∑ q ∈ Finset.Ico (4 * m) (5 * m) ∪
            (Finset.Ico (4 * m + 1) (5 * m)).image (fun q => 8 * m - q),
            w q * w (8 * m - q) :=
        (Finset.sum_union (by
          rw [Finset.disjoint_left]
          intro q hq hmem
          simp only [Finset.mem_image] at hmem
          obtain ⟨q', hq', rfl⟩ := hmem
          exact (hQ1 q' hq').2 _ hq rfl)).symm
      _ ≤ ∑ q ∈ (Finset.range (8 * m + 1)).filter (fun q => 8 * m ≤ 3 * q ∧ 3 * q ≤ 2 * (8 * m)),
            w q * w (8 * m - q) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.union_subset (fun q hq => hQ0 q hq) (fun r hr => by
            simp only [Finset.mem_image] at hr
            obtain ⟨q', hq', rfl⟩ := hr
            exact (hQ1 q' hq').1))
          (fun q _ _ => mul_nonneg (hw _) (hw _))
  -- the block mass products pay for the additive constant
  have hterm : ∀ j ∈ Finset.range B,
      2 * ((H : ℝ) * C j - A j * D j) / (2 * (H : ℝ)) = C j - A j * D j / (H : ℝ) := by
    intro j _
    field_simp
  have hlow : ((8 * m : ℕ) : ℝ) / 32 ≤ ∑ j ∈ Finset.range B, (A j * D j / (H : ℝ)) := by
      calc ((8 * m : ℕ) : ℝ) / 32 = ((B * H : ℕ) : ℝ) / 4 := by rw [hBH]; push_cast; ring
        _ = ∑ j ∈ Finset.range B, ((H : ℝ) / 4) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
        _ ≤ ∑ j ∈ Finset.range B, (A j * D j / (H : ℝ)) := by
            refine Finset.sum_le_sum (fun j hj => ?_)
            have hA0 : 0 ≤ A j := le_trans (by positivity) (hA2 j hj)
            have h1 : ((H : ℝ) / 2) * ((H : ℝ) / 2) ≤ A j * D j :=
              mul_le_mul (hA2 j hj) (hD2 j hj) (by positivity) hA0
            have h2 : (((H : ℝ) / 2) * ((H : ℝ) / 2)) / (H : ℝ) ≤ A j * D j / (H : ℝ) := by
              rw [div_eq_mul_inv, div_eq_mul_inv]
              exact mul_le_mul_of_nonneg_right h1 (by positivity)
            calc (H : ℝ) / 4 = (((H : ℝ) / 2) * ((H : ℝ) / 2)) / (H : ℝ) := by
                  field_simp
                  ring
              _ ≤ A j * D j / (H : ℝ) := h2
  have hL1 : (∑ j ∈ Finset.range B, (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
          (w (4 * m + j * H + s) - w (4 * m + j * H + t)) *
            (w (8 * m - (4 * m + j * H + s)) - w (8 * m - (4 * m + j * H + t)))) / (2 * (H : ℝ)))
      = ∑ j ∈ Finset.range B, (C j - A j * D j / (H : ℝ)) := by
    have h1 : ∀ j ∈ Finset.range B, ((∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
          (w (4 * m + j * H + s) - w (4 * m + j * H + t)) *
            (w (8 * m - (4 * m + j * H + s)) - w (8 * m - (4 * m + j * H + t)))) / (2 * (H : ℝ)))
        = (C j - A j * D j / (H : ℝ)) := by
      intro j hj
      rw [ident j hj]
      exact hterm j hj
    exact Finset.sum_congr rfl h1
  rw [hL1, Finset.sum_sub_distrib, hCsplit]
  have hS0 : 0 ≤ ∑ q ∈ Finset.Ico (4 * m) (5 * m), w q * w (8 * m - q) :=
    Finset.sum_nonneg (fun q _ => mul_nonneg (hw _) (hw _))
  linarith

end Conjectures.Goldbach.DyadicCellWindowTransfer_aux

theorem Conjectures.Goldbach.DyadicCellWindowTransfer : let w := fun p : ℕ => if Nat.Prime p then Real.log (p : ℝ) else 0; ∀ k : ℕ, 12 ≤ k → let n : ℕ := 2^k; let H : ℕ := 2^(k-k/4); let B : ℕ := 2^(k/4-3); let p := fun j t : ℕ => n/2+j*H+t; let a := fun j t : ℕ => w (p j t); let b := fun j t : ℕ => w (n-p j t); (∀ x : ℕ, n ≤ 3*x → 3*x ≤ 2*n → (H:ℝ)/2 ≤ ∑ t ∈ Finset.range H, w (x+t)) → (n:ℝ)/32 + (∑ j ∈ Finset.range B, (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, (a j s-a j t)*(b j s-b j t)) / (2*(H:ℝ))) ≤ (∑ p ∈ (Finset.range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n), w p * w (n-p)) := by
  intro w k hk
  have hm : 2 ^ k = 8 * 2 ^ (k - 3) := by
    rw [show (8 : ℕ) = 2 ^ 3 from by norm_num, ← pow_add, show 3 + (k - 3) = k from by omega]
  rw [hm]
  dsimp only
  refine Conjectures.Goldbach.DyadicCellWindowTransfer_aux.blockTransfer w ?_ (2 ^ (k - 3)) (2 ^ (k - k / 4)) (2 ^ (k / 4 - 3)) ?_ ?_ ?_ ?_
  · intro q
    simp only [w]
    split_ifs with hq
    · exact Real.log_nonneg (by exact_mod_cast Nat.Prime.pos hq)
    · exact le_rfl
  · positivity
  · positivity
  · rw [← pow_add, show (k / 4 - 3) + (k - k / 4) = k - 3 from by omega]
  · have h2 : 4 * 2 ^ (k - 3) = 2 ^ (k - 1) := by
      show 2 ^ 2 * 2 ^ (k - 3) = 2 ^ (k - 1)
      rw [← pow_add, show 2 + (k - 3) = k - 1 from by omega]
    show w (4 * 2 ^ (k - 3)) = 0
    rw [h2]
    simp only [w]
    split_ifs with hp
    · exact absurd hp (Nat.Prime.not_prime_pow (by omega))
    · rfl
