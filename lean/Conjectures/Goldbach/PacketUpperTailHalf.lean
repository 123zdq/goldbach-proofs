import Mathlib

open MeasureTheory Finset

namespace Goldbach.PacketTail
noncomputable section

/-- The doubling-orbit moment argument is adapted from the repository's
`Goldbach.LacunarySpectrum` development in `BinaryShiftLargeSpectrum.lean`. -/
def orbit (g : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun t => g t + orbit g n (2 * t)

theorem orbit_cont {g : ℝ → ℝ} (hg : Continuous g) (n : ℕ) : Continuous (orbit g n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact hg.add (ih.comp (continuous_const.mul continuous_id))

theorem orbit_period {g : ℝ → ℝ} (hg : ∀ t, g (t + 1) = g t) (n : ℕ) (t : ℝ) :
    orbit g n (t + 1) = orbit g n t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    simp only [orbit, hg, show 2 * (t + 1) = 2 * t + 1 + 1 by ring, ih]

theorem halves (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ t in (0 : ℝ)..1, f t) =
      (1 / 2 : ℝ) * (∫ t in (0 : ℝ)..1, f ((1 / 2) * t) + f ((1 / 2) * t + 1 / 2)) := by
  have h1 := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1) f
    (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have h2 := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := 1) f
    (by norm_num : (1 / 2 : ℝ) ≠ 0) (1 / 2)
  rw [intervalIntegral.integral_add
    (by exact (hf.comp (continuous_const.mul continuous_id)).intervalIntegrable ..)
    (by exact (hf.comp ((continuous_const.mul continuous_id).add continuous_const)).intervalIntegrable ..)]
  rw [h1, h2]
  norm_num
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable (0 : ℝ) (1 / 2)) (hf.intervalIntegrable (1 / 2) (1 : ℝ))
  linarith only [h]

theorem exp_moment {g : ℝ → ℝ} (hg : Continuous g) (hs : ∀ t, g (t + 1 / 2) = -g t)
    (hb : ∀ t, |g t| ≤ 1) (n : ℕ) :
    (∫ t in (0 : ℝ)..1, Real.exp (orbit g n t / 2)) ≤ Real.exp ((n : ℝ) / 8) := by
  have per (t : ℝ) : g (t + 1) = g t := by
    rw [show t + 1 = t + 1 / 2 + 1 / 2 by ring, hs, hs, neg_neg]
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
    let f := fun t => Real.exp (orbit g (n + 1) t / 2)
    have hf : Continuous f := Real.continuous_exp.comp ((orbit_cont hg _).div_const _)
    have pair (t : ℝ) : f ((1 / 2) * t) + f ((1 / 2) * t + 1 / 2) ≤
        2 * Real.exp (1 / 8) * Real.exp (orbit g n t / 2) := by
      have halve_add (x y : ℝ) : (x + y) / 2 = x / 2 + y / 2 := by ring
      simp only [f, orbit, hs, show 2 * ((1 / 2) * t) = t by ring,
        show 2 * ((1 / 2) * t + 1 / 2) = t + 1 by ring, orbit_period per,
        halve_add, Real.exp_add, neg_div]
      have hsq := (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr (hb ((1 / 2) * t))
      rw [sq_abs] at hsq
      have hcos := (Real.cosh_le_exp_half_sq (g ((1 / 2) * t) / 2)).trans
        (Real.exp_le_exp.mpr (by nlinarith only [hsq] :
          (g ((1 / 2) * t) / 2) ^ 2 / 2 ≤ 1 / 8))
      rw [Real.cosh_eq] at hcos
      nlinarith only [mul_le_mul_of_nonneg_right hcos (Real.exp_pos (orbit g n t / 2)).le]
    change (∫ t in (0 : ℝ)..1, f t) ≤ _
    rw [halves f hf]
    have him := intervalIntegral.integral_mono_on (μ := volume) (a := (0 : ℝ)) (b := 1)
      (by norm_num)
      (by exact ((hf.comp (continuous_const.mul continuous_id)).add
        (hf.comp ((continuous_const.mul continuous_id).add continuous_const))).intervalIntegrable ..)
      (by apply Continuous.intervalIntegrable
          exact continuous_const.mul (Real.continuous_exp.comp ((orbit_cont hg n).div_const 2)))
      (fun t _ => pair t)
    rw [intervalIntegral.integral_const_mul] at him
    have hprod := mul_le_mul_of_nonneg_left ih (Real.exp_pos (1 / 8)).le
    rw [Nat.cast_succ, show ((n : ℝ) + 1) / 8 = 1 / 8 + n / 8 by ring, Real.exp_add]
    linarith only [him, hprod]

def phase (t : ℝ) : ℂ := Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)

theorem phase_cont : Continuous phase := by
  unfold phase
  fun_prop

def spectrum (n : ℕ) (t : ℝ) : ℂ := ∑ j ∈ range n, phase ((2 : ℝ) ^ j * t)

theorem spectrum_cont (n : ℕ) : Continuous (spectrum n) := by
  unfold spectrum
  exact continuous_finsetSum _ (fun j _ => phase_cont.comp (continuous_const.mul continuous_id))

theorem projection (p : ℂ →L[ℝ] ℝ) (n : ℕ) (t : ℝ) :
    p (spectrum n t) = orbit (fun x => p (phase x)) n t := by
  induction n generalizing t with
  | zero => simp [orbit, spectrum]
  | succ n ih =>
    change p (spectrum (n + 1) t) = p (phase t) + orbit _ n (2 * t)
    rw [← ih]
    simp only [spectrum, sum_range_succ', pow_zero, one_mul, map_add, pow_succ, mul_assoc]
    apply add_comm

theorem moment (p : ℂ →L[ℝ] ℝ) (hp : ∀ z, |p z| ≤ ‖z‖) (n : ℕ) :
    (∫ t in (0 : ℝ)..1, Real.exp (p (spectrum n (2 * t)) / 2)) ≤ Real.exp ((n : ℝ) / 8) := by
  let g := fun x => p (phase x)
  have hs (t : ℝ) : g (t + 1 / 2) = -g t := by
    simp only [g, phase, show 2 * Real.pi * (t + 1 / 2) = 2 * Real.pi * t + Real.pi by ring,
      Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one, map_neg]
  have hper (t : ℝ) : g (t + 1) = g t := by
    rw [show t + 1 = t + 1 / 2 + 1 / 2 by ring, hs, hs, neg_neg]
  have hb (t : ℝ) : |g t| ≤ 1 := (hp _).trans_eq (Complex.norm_exp_ofReal_mul_I _)
  have hg : Continuous g := p.continuous.comp phase_cont
  let f := fun t => Real.exp (orbit g n t / 2)
  have hf : Continuous f := Real.continuous_exp.comp ((orbit_cont hg n).div_const 2)
  simp_rw [projection]
  change (∫ t in (0 : ℝ)..1, f (2 * t)) ≤ _
  rw [halves (fun t => f (2 * t)) (hf.comp (continuous_const.mul continuous_id))]
  have fp (t : ℝ) : f (t + 1) = f t := by simp only [f, orbit_period hper]
  simp only [show ∀ t : ℝ, 2 * (1 / 2 * t) = t by intro t; ring,
    show ∀ t : ℝ, 2 * (1 / 2 * t + 1 / 2) = t + 1 by intro t; ring, fp]
  rw [intervalIntegral.integral_add (hf.intervalIntegrable ..) (hf.intervalIntegrable ..)]
  linarith only [show (∫ t in (0 : ℝ)..1, f t) ≤ Real.exp ((n : ℝ) / 8) from
    exp_moment hg hs hb n]

end
end Goldbach.PacketTail

open Goldbach.PacketTail in
theorem Conjectures.Goldbach.PacketUpperTailHalf : let T := fun (m : ℕ) (t : ℝ) => ∑ j ∈ Finset.range m, Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t); ∀ m : ℕ, 0 < m → intervalIntegral (fun t => if (m:ℝ)/2 < T m t then (1:ℝ) else 0) (0:ℝ) 1 MeasureTheory.volume ≤ Real.exp (-(m:ℝ)/8) := by
  intro T m _
  let S := fun t => spectrum m (2 * t)
  let A := fun t => if (m : ℝ) / 2 < T m t then (1 : ℝ) else 0
  let E := fun t => Real.exp (Complex.reCLM (S t) / 2)
  let w := Real.exp ((m : ℝ) / 4)
  have hS : Continuous S := (spectrum_cont m).comp (continuous_const.mul continuous_id)
  have hTc : Continuous (T m) := by
    dsimp only [T]
    fun_prop
  have hT (t : ℝ) : T m t = Complex.reCLM (S t) := by
    change (∑ j ∈ range m, Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) =
      (spectrum m (2 * t)).re
    rw [Goldbach.PacketTail.spectrum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    change _ = (phase ((2 : ℝ) ^ j * (2 * t))).re
    unfold phase
    rw [Complex.exp_ofReal_mul_I_re]
    congr 1
    rw [pow_succ]
    ring
  have hE (t : ℝ) : E t = Real.exp (T m t / 2) := by
    dsimp only [E]
    rw [← hT t]
  have hEc : Continuous E :=
    Real.continuous_exp.comp ((Complex.reCLM.continuous.comp hS).div_const _)
  have hEi : IntervalIntegrable E volume 0 1 := hEc.intervalIntegrable ..
  have hA : IntervalIntegrable A volume 0 1 := by
    apply (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
    · exact (measurable_const.ite (measurableSet_lt measurable_const hTc.measurable)
        measurable_const).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun t => by dsimp [A]; split <;> norm_num)
  have pt (t : ℝ) : w * A t ≤ E t := by
    dsimp only [A]
    split_ifs with h
    · rw [mul_one, hE]
      dsimp only [w]
      exact Real.exp_le_exp.mpr (by linarith)
    · simp only [mul_zero]
      exact (Real.exp_pos _).le
  have hint := intervalIntegral.integral_mono_on (μ := volume) (a := (0 : ℝ)) (b := 1)
    (by norm_num) (hA.const_mul w) hEi (fun t _ => pt t)
  rw [intervalIntegral.integral_const_mul] at hint
  have hmoment : (∫ t in (0 : ℝ)..1, E t) ≤ Real.exp ((m : ℝ) / 8) := by
    simpa only [E, S] using moment Complex.reCLM Complex.abs_re_le_norm m
  have htot : w * (∫ t in (0 : ℝ)..1, A t) ≤ Real.exp ((m : ℝ) / 8) := hint.trans hmoment
  change (∫ t in (0 : ℝ)..1, A t) ≤ Real.exp (-(m : ℝ) / 8)
  apply le_of_mul_le_mul_left (a := w) _ (Real.exp_pos _)
  convert htot using 1
  dsimp only [w]
  rw [← Real.exp_add]
  congr 2
  ring
