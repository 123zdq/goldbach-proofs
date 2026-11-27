import Mathlib

/-!
JA-0021：三个指定余类张成整个三维商格。

在 `(ZMod 29)³` 中取向量 `(1,0,0)`、`(0,1+z²,0)`、`(1,0,z²)`，其中 `z = 7`。
它们构成对角元为单位的上三角矩阵（`1+z² = 21`，`z² = 20`），故线性无关；
向量个数等于空间维数 3，所以张成全空间。
-/

theorem Conjectures.JoshiAbc.ThreeJetSpan : let z : ZMod 29 := 7; let v : Fin 3 → Fin 3 → ZMod 29 := ![![1,0,0],![0,1+z^2,0],![1,0,z^2]]; Submodule.span (ZMod 29) (Set.range v) = ⊤ := by
  intro z v
  -- 数值事实（先于域结构实例建立，便于 `decide` 求值）
  have hz : z = (7 : ZMod 29) := rfl
  have hz2 : z ^ 2 = (20 : ZMod 29) := by rw [hz]; decide
  have h12 : 1 + z ^ 2 = (21 : ZMod 29) := by rw [hz]; decide
  have n21 : (21 : ZMod 29) ≠ 0 := by decide
  have n20 : (20 : ZMod 29) ≠ 0 := by decide
  -- 三个向量的分量（按定义化简）
  have v00 : v 0 = ![1, 0, 0] := rfl
  have v01 : v 1 = ![0, 1 + z ^ 2, 0] := rfl
  have v02 : v 2 = ![1, 0, z ^ 2] := rfl
  -- 29 为素数：此后 `ZMod 29` 作为域使用
  have : Fact (Nat.Prime 29) := ⟨by decide⟩
  have hv : LinearIndependent (ZMod 29) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have c0 : g 0 + g 2 = 0 := by
      have := congrFun hg 0
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three, v00, v01, v02,
        Matrix.cons_val_zero, mul_one, mul_zero, add_zero, Pi.zero_apply] at this
      exact this
    have c1 : g 1 * 21 = 0 := by
      have := congrFun hg 1
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three, v00, v01, v02,
        Matrix.cons_val_one, Matrix.cons_val_zero, mul_zero, zero_add, add_zero, Pi.zero_apply,
        h12] at this
      exact this
    have c2 : g 2 * 20 = 0 := by
      have := congrFun hg 2
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three, v00, v01, v02,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_zero, zero_add, add_zero,
        Pi.zero_apply, hz2] at this
      exact this
    have e1 : g 1 = 0 := by
      rw [mul_eq_zero] at c1
      exact c1.resolve_right n21
    have e2 : g 2 = 0 := by
      rw [mul_eq_zero] at c2
      exact c2.resolve_right n20
    have e0 : g 0 = 0 := by
      rw [e2, add_zero] at c0
      exact c0
    fin_cases i
    · exact e0
    · exact e1
    · exact e2
  exact hv.span_eq_top_of_card_eq_finrank (by simp)
