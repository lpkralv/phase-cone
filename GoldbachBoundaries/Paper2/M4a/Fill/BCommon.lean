import GoldbachBoundaries.Paper2.M4a.Fill.segment_subset_Str
import GoldbachBoundaries.ThmA.Fill.CCommon

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
open scoped Interval
namespace GoldbachBoundaries.Paper2.M4a
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

namespace GroupB

theorem isOpen_domain (A : Aff) {U : Set ℂ} (hU : IsOpen U) :
    IsOpen {p : ℂ × ℂ | p.2 ∈ U ∧ p.1 ∈ A.Str p.2} := by
  exact (hU.preimage continuous_snd).inter
    ((isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).inter
      (isOpen_lt (Complex.continuous_re.comp continuous_fst)
        ((continuous_app_re A).comp continuous_snd)))

theorem param_mem (A : Aff) {a b : ℂ} (ha : a ∈ PoleSetQ) (hb : b ∈ PoleSetQ)
    {s : ℂ} (hs : s ∈ A.HL) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    a + (t : ℂ) * (A.app s - a - b) ∈ A.Str s := by
  apply segment_subset_Str A ha hb hs
  rw [segment_eq_image']
  refine ⟨t, ht, ?_⟩
  simp only [Complex.real_smul]
  congr 2; ring

theorem differentiableOn_integral (A : Aff) (k : ℂ → ℂ → ℂ) {U : Set ℂ}
    (hU : IsOpen U) (hUH : U ⊆ A.HL)
    (hk : DifferentiableOn ℂ (fun p : ℂ × ℂ => k p.1 p.2)
      {p | p.2 ∈ U ∧ p.1 ∈ A.Str p.2})
    {a b : ℂ} (ha : a ∈ PoleSetQ) (hb : b ∈ PoleSetQ) :
    DifferentiableOn ℂ (fun s => ∫ t in (0 : ℝ)..1,
      k (a + (t : ℂ) * (A.app s - a - b)) s) U := by
  have hmem : ∀ s ∈ U, ∀ t ∈ [[(0 : ℝ), 1]],
      (a + (t : ℂ) * (A.app s - a - b), s) ∈
        {p : ℂ × ℂ | p.2 ∈ U ∧ p.1 ∈ A.Str p.2} := by
    intro s hs t ht
    exact ⟨hs, param_mem A ha hb (hUH hs) (by simpa using ht)⟩
  apply GoldbachBoundaries.ThmA.differentiableOn_intervalIntegral_of_continuousOn hU
  · rintro ⟨s, t⟩ ⟨hs, ht⟩
    exact ((hk.differentiableAt ((isOpen_domain A hU).mem_nhds (hmem s hs t ht))).continuousAt.comp
      (f := fun p : ℂ × ℝ => (a + (p.2 : ℂ) * (A.app p.1 - a - b), p.1))
      (show ContinuousAt (fun p : ℂ × ℝ =>
        (a + (p.2 : ℂ) * (A.app p.1 - a - b), p.1)) (s, t) by
          unfold Aff.app; fun_prop)).continuousWithinAt
  · intro t ht s hs
    exact ((hk.differentiableAt ((isOpen_domain A hU).mem_nhds (hmem s hs t ht))).comp s
      (f := fun x : ℂ => (a + (t : ℂ) * (A.app x - a - b), x))
      (show DifferentiableAt ℂ (fun x : ℂ =>
        (a + (t : ℂ) * (A.app x - a - b), x)) s by
          unfold Aff.app; fun_prop)).differentiableWithinAt

end GroupB
end GoldbachBoundaries.Paper2.M4a
