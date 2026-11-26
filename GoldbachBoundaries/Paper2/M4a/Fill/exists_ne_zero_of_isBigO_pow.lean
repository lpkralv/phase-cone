import GoldbachBoundaries.Paper2.M4a.H2log

/-!
# Fill (group C): `exists_ne_zero_of_isBigO_pow`

A leading term `c(s - α)^m`, `c ≠ 0`, is not cancelled. If `f = 0` on `U ∈ 𝓝 α`, the hypothesis gives
`-c(s - α)^m = O((s - α)^{m+1}) = o((s - α)^m)`, so on the punctured neighbourhood `-c = (-c(s - α)^m)/(s - α)^m → 0`,
i.e. `c = 0`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **A leading term `c(s - α)^m`, `c ≠ 0`, is not cancelled** (general). If `f = 0` on `U ∈ 𝓝 α`, the hypothesis
gives `‖c‖‖s - α‖^m ≤ C‖s - α‖^{m+1}` for `s` near `α` (`IsBigO.bound`), i.e. `‖c‖ ≤ C‖s - α‖` for `s ≠ α` near
`α`; take `s = α + η` with `0 < η < ‖c‖/(C + 1)` small (or a sequence `s → α`, `s ≠ α`), a contradiction.
Size: 50–100 lines. -/
theorem exists_ne_zero_of_isBigO_pow {f : ℂ → ℂ} {α c : ℂ} {m : ℕ} (hc : c ≠ 0)
    (h : (fun s => f s - c * (s - α) ^ m) =O[𝓝 α] fun s => (s - α) ^ (m + 1)) {U : Set ℂ} (hU : U ∈ 𝓝 α) :
    ∃ s ∈ U, f s ≠ 0 := by
  by_contra hne
  simp only [not_exists, not_and, not_not] at hne
  -- `(s - α)^{m+1} = o((s - α)^m)` at `α`
  have hpow : (fun s : ℂ => (s - α) ^ (m + 1)) =o[𝓝 α] fun s => (s - α) ^ m := by
    have h0 := isLittleO_pow_pow (𝕜 := ℂ) (Nat.lt_succ_self m)
    have ht : Tendsto (fun s : ℂ => s - α) (𝓝 α) (𝓝 0) :=
      tendsto_sub_nhds_zero_iff.2 tendsto_id
    exact h0.comp_tendsto ht
  have hlo := (h.trans_isLittleO hpow).mono (nhdsWithin_le_nhds (s := {α}ᶜ))
  have htend := hlo.tendsto_div_nhds_zero
  have hev : (fun s => (f s - c * (s - α) ^ m) / (s - α) ^ m) =ᶠ[𝓝[≠] α] fun _ => -c := by
    filter_upwards [nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with s hs hsα
    have hsα' : (s - α) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hsα)
    rw [hne s hs, zero_sub, neg_div, mul_div_assoc, div_self hsα', mul_one]
  have hlim : Tendsto (fun _ : ℂ => -c) (𝓝[≠] α) (𝓝 0) := htend.congr' hev
  have := tendsto_nhds_unique tendsto_const_nhds hlim
  exact hc (neg_eq_zero.1 this)

end GoldbachBoundaries.Paper2.M4a
