/- Adapted from a pilot built on the zeta project by Mercuri and Mehta
   (Apache-2.0); uses its certified evaluation. -/

module

public import GoldbachBoundaries.LowZeros.Brackets
public import GoldbachBoundaries.LowZeros.Endpoints
public import GoldbachBoundaries.LowZeros.Gram
public import GoldbachBoundaries.LowZeros.TailEM
public import GoldbachBoundaries.LowZeros.TailRS1
public import GoldbachBoundaries.LowZeros.TailRS2
public import GoldbachBoundaries.LowZeros.TailRS3
public import Zeta.Zeros.RiemannHypothesisUpTo.Basic

@[expose] public section

namespace Pilot

open Complex Set Zeta.Certificates Zeta.Certificates.Gram

theorem bracket_width (i : Fin 4) : hi i - lo i = (1 / 10 ^ 30 : ℝ) := by
  fin_cases i <;> norm_num [lo, hi, start]

private theorem bracket_bounds (i : Fin 4) : 0 ≤ lo i ∧ lo i ≤ hi i ∧ hi i < 32 := by
  fin_cases i <;> norm_num [lo, hi, start]

private theorem bracket_separated (i j : Fin 4) (h : i < j) : hi i ≤ lo j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.lt_def] at h <;> norm_num [lo, hi, start]

private noncomputable def interval (i : Fin 4) : NonemptyInterval ℝ :=
  ⟨(lo i, hi i), (bracket_bounds i).2.1⟩

private theorem singleBatch_has_zero {an ad bn bd : ℕ} (h : BatchSpec 1 an ad bn bd) :
    ∃ t ∈ Ioo (Enclosure.sfrac false an ad) (Enclosure.sfrac false bn bd),
      riemannZeta (1 / 2 + I * t) = 0 := by
  obtain ⟨C, hlen, hlo, hhi⟩ := h
  obtain ⟨J, hJ⟩ := List.length_eq_one_iff.mp hlen
  simp [hJ] at hlo hhi
  simpa only [hlo, hhi] using C.has_zero J (by simp [hJ])

private theorem interval_has_zero (i : Fin 4) :
    ∃ t ∈ Ioo (lo i) (hi i), riemannZeta (1 / 2 + I * t) = 0 := by
  fin_cases i
  · have h := singleBatch_has_zero bracket1
    simp only [Enclosure.sfrac_false_div] at h
    exact h
  · have h := singleBatch_has_zero bracket2
    simp only [Enclosure.sfrac_false_div] at h
    exact h
  · have h := singleBatch_has_zero bracket3
    simp only [Enclosure.sfrac_false_div] at h
    exact h
  · have h := singleBatch_has_zero bracket4
    simp only [Enclosure.sfrac_false_div] at h
    exact h

private noncomputable def low : CertifiedZeroIntervals where
  intervals := List.ofFn interval
  fst_nonneg := by
    intro J hJ
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hJ
    exact (bracket_bounds i).1
  has_zero := by
    intro J hJ
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hJ
    exact interval_has_zero i
  disj := by
    have h : (List.ofFn interval).Pairwise (fun A B => A.snd ≤ B.fst) := by
      apply List.pairwise_iff_getElem.mpr
      intro a b ha hb hab
      simp only [List.getElem_ofFn]
      exact bracket_separated _ _ hab
    exact h.isChain

private noncomputable abbrev tailBatches : List CertifiedZeroIntervals :=
  [tailEM.bundle, tailRS1.bundle, tailRS2.bundle, tailRS3.bundle]

private noncomputable def upper : CertifiedZeroIntervals :=
  CertifiedZeroIntervals.join tailBatches
    (by simp [tailBatches, tailEM.bundle_ne, tailRS1.bundle_ne,
      tailRS2.bundle_ne, tailRS3.bundle_ne])
    (by
      simp only [tailBatches, List.isChain_cons_cons, List.isChain_singleton, and_true]
      exact ⟨separated_of_endpoints tailEM.bundle_getLast? tailRS1.bundle_head? le_rfl,
        separated_of_endpoints tailRS1.bundle_getLast? tailRS2.bundle_head? le_rfl,
        separated_of_endpoints tailRS2.bundle_getLast? tailRS3.bundle_head? le_rfl⟩)

private theorem upper_left : upper.intervals.head?.map (·.fst) = some (32.5 : ℝ) := by
  rw [upper, CertifiedZeroIntervals.join_intervals]
  simp only [tailBatches, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil]
  rw [List.head?_append_of_ne_nil _ tailEM.bundle_ne, tailEM.bundle_head?]
  congr 1
  norm_num [Enclosure.sfrac]

private theorem upper_left_le (J : NonemptyInterval ℝ) (hJ : J ∈ upper.intervals) :
    (32.5 : ℝ) ≤ J.fst := by
  obtain ⟨A, hA, hAfst⟩ := Option.map_eq_some_iff.mp upper_left
  obtain ⟨rest, hrest⟩ := List.head?_eq_some_iff.mp hA
  rw [hrest, List.mem_cons] at hJ
  rcases hJ with rfl | hJ
  · exact hAfst.ge
  · have hp := upper.pairwise
    rw [hrest, List.pairwise_cons] at hp
    exact hAfst.ge.trans (A.fst_le_snd.trans (hp.1 J hJ))

private theorem seam : Separated low upper := by
  intro A hA B hB
  have ha : A ∈ low.intervals := List.mem_of_mem_getLast? hA
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  have hb : B ∈ upper.intervals := List.mem_of_mem_head? hB
  exact (bracket_bounds i).2.2.le.trans ((by norm_num : (32 : ℝ) ≤ 32.5).trans (upper_left_le B hb))

private noncomputable def count : CertifiedZeroCount where
  toCertifiedGramBlockSeq := certifiedGramBlockSeq
  toCertifiedZeroIntervals := low.append upper seam
  count := by
    change 289 + 1 = (low.intervals ++ upper.intervals).length
    rw [List.length_append, upper, CertifiedZeroIntervals.join_intervals]
    simp [low, tailBatches]
  below := by
    apply (low.append upper seam).height_le_of_getLast?_snd
    · have hne : upper.intervals ≠ [] := by
        intro h
        have h' := upper_left
        simp [h] at h'
      rw [CertifiedZeroIntervals.append_getLast? _ _ _ hne]
      rw [upper, CertifiedZeroIntervals.join_getLast?]
      exact tailRS3.bundle_getLast?
    · refine le_trans ?_ certifiedGramBlockSeq.head_left_le_gramPoint
      change Enclosure.sfrac false 529115 1000 ≤ (gp1.fst : ℝ)
      norm_num [gp1, Enclosure.sfrac]

theorem gram_count : riemannZeta.N (gramPoint 289) = 290 := by
  have h := riemannZeta.N_gramPoint_eq count
  have hlen : count.intervals.length = 290 := count.count.symm
  change riemannZeta.N (gramPoint count.minIdx) = 290
  simpa only [hlen, Nat.cast_ofNat] using h

private theorem height_lt_head : (32 : ℝ) < gramPoint count.minIdx :=
  (by norm_num [gp1] : (32 : ℝ) < gp1.fst).trans_le certifiedGramBlockSeq.head_left_le_gramPoint

private theorem all_mem_zeros {z : ℂ} (hz : riemannZeta z = 0)
    (ht : z.im ∈ Ioo 0 (gramPoint count.minIdx)) : z ∈ count.zeros := by
  by_contra h
  have hn := riemannZeta.le_N_of_zeros (z :: count.zeros) (by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact ⟨ht, hz⟩
    · obtain ⟨hheight, hzero⟩ := count.zeros_spec w hw
      exact ⟨⟨hheight.1, hheight.2.trans_le count.below⟩, hzero⟩)
    (List.nodup_cons.mpr ⟨h, count.zeros_nodup⟩)
  rw [riemannZeta.N_gramPoint_eq count] at hn
  simp only [List.length_cons, count.zeros_length, Nat.cast_add, Nat.cast_one] at hn
  linarith

private theorem interval_mem (i : Fin 4) : interval i ∈ count.intervals := by
  change interval i ∈ low.intervals ++ upper.intervals
  exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

private noncomputable def zero (i : Fin 4) : ℂ :=
  1 / 2 + I * (count.has_zero (interval i) (interval_mem i)).choose

private theorem zero_spec (i : Fin 4) :
    (zero i).im ∈ Ioo (lo i) (hi i) ∧ (zero i).re = 1 / 2 ∧ riemannZeta (zero i) = 0 := by
  have h := (count.has_zero (interval i) (interval_mem i)).choose_spec
  exact ⟨by simpa [zero, interval] using h.1, by simp [zero], h.2⟩

/-- Exactly four simple critical-line zeros have positive height at most 32. -/
theorem zerosThrough32 :
    ∃ ρ : Fin 4 → ℂ, Function.Injective ρ ∧
      (∀ i, (ρ i).im ∈ Ioo (lo i) (hi i) ∧ (ρ i).re = 1 / 2 ∧
        meromorphicOrderAt riemannZeta (ρ i) = 1) ∧
      {z : ℂ | riemannZeta z = 0 ∧ z.im ∈ Ioc 0 32} = Set.range ρ := by
  have hpos (i : Fin 4) : (zero i).im ∈ Ioc 0 32 :=
    ⟨(bracket_bounds i).1.trans_lt (zero_spec i).1.1,
      ((zero_spec i).1.2.trans (bracket_bounds i).2.2).le⟩
  refine ⟨zero, ?_, ?_, ?_⟩
  · have hmono : StrictMono (fun i => (zero i).im) := by
      intro i j hij
      exact ((zero_spec i).1.2.trans_le (bracket_separated i j hij)).trans (zero_spec j).1.1
    exact hmono.injective.of_comp (f := Complex.im)
  · intro i
    obtain ⟨hI, hre, hz⟩ := zero_spec i
    exact ⟨hI, hre, riemannZeta.meromorphicOrderAt_eq_one_upto count
      ⟨(hpos i).1, (hpos i).2.trans_lt height_lt_head⟩ hz⟩
  · ext z
    constructor
    · rintro ⟨hz, ht⟩
      have hmem := all_mem_zeros hz ⟨ht.1, ht.2.trans_lt height_lt_head⟩
      simp only [CertifiedZeroIntervals.zeros, List.mem_map, List.mem_pmap] at hmem
      obtain ⟨_, ⟨J, hJ, rfl⟩, rfl⟩ := hmem
      change J ∈ low.intervals ++ upper.intervals at hJ
      rcases List.mem_append.mp hJ with hlow | hupp
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hlow
        exact ⟨i, rfl⟩
      · have hgt := (upper_left_le J hupp).trans_lt (count.has_zero J hJ).choose_spec.1.1
        have hle : (count.has_zero J hJ).choose ≤ 32 := by simpa using ht.2
        linarith
    · rintro ⟨i, rfl⟩
      exact ⟨(zero_spec i).2.2, hpos i⟩

end Pilot

#print axioms riemannZeta.N_gramPoint_eq
#print axioms simpleZerosUpTo
#print axioms Pilot.gram_count
#print axioms Pilot.bracket_width
/-- info: 'Pilot.zerosThrough32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Pilot.zerosThrough32
