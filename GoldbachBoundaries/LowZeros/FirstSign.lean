/- Adapted from a pilot built on the zeta project by Mercuri and Mehta
   (Apache-2.0); uses its certified evaluation. -/

module

public import GoldbachBoundaries.LowZeros.Endpoints
public import Zeta.Certificate.Named
public import Zeta.Zeros.HardyZ
meta import Zeta.Certificate.Named

@[expose] public section

namespace Pilot

open Lean Elab Tactic BSN

private abbrev first := 14134725141734693790457251983562
private noncomputable abbrev t : ℝ := Enclosure.sfrac false first (10 ^ 30)

-- Enclose the approximant plus its error and the requested strict margin.
local elab "check_first_left " n:num : tactic => do
  let first := n.getNat
  let endpoint := sfracExpr false first (10 ^ 30)
  let ht := mkReflR endpoint
  let precision := 10 ^ 35
  let value ← mkHardyZCached endpoint ht first (10 ^ 30) 50 128 precision
  let error ← mkErrStrongNamed endpoint ht first (10 ^ 30) 50 128 precision
  let upper ← addNear (← addNear value error) (← mkConstNear 3 (10 ^ 31))
  unless upper.neg && upper.rn * upper.cd < upper.cn * upper.rd do
    throwError "The enclosure does not establish the requested margin"
  let proof := mkAppN (mkConst ``Enclosure.Real.IsNear.neg_val)
    #[upper.x, mkNatLit upper.cn, mkNatLit upper.cd, mkNatLit upper.rn, mkNatLit upper.rd,
      upper.proof, BSN.reflBoolTrue, BSN.reflBoolTrue, BSN.reflBoolTrue]
  liftMetaFinishingTactic (·.assign proof)

private theorem approximant_margin :
    hardyZApproximantEM 50 128 t + hardyZErrorBoundStrong 50 128 t +
      Enclosure.sfrac false 3 (10 ^ 31) < 0 := by check_first_left 14134725141734693790457251983562

/-- The Hardy value at the paper's first left endpoint, including its Euler–Maclaurin error. -/
theorem first_left_margin : Zeta.hardyZ (lo 0) < -(3 / 10 ^ 31 : ℝ) := by
  have ht : lo 0 = t := by
    norm_num [lo, start, t, first, Enclosure.sfrac]
  rw [ht]
  have h := abs_hardyZRemainderEM_le (M := 50) (N := 128) (t := t)
    (by decide) (by decide) (by norm_num [t, Enclosure.sfrac])
  have he := (abs_le.mp h).2.trans (hardyZErrorBoundEM_le_strong 50 128 t rfl)
  have hid : Zeta.hardyZ t = hardyZApproximantEM 50 128 t + hardyZRemainderEM 50 128 t := by
    rw [hardyZRemainderEM]
    ring
  have hm := approximant_margin
  rw [show Enclosure.sfrac false 3 (10 ^ 31) = (3 / 10 ^ 31 : ℝ) by
    norm_num [Enclosure.sfrac]] at hm
  linarith only [he, hid, hm]

end Pilot

/-- info: 'Pilot.first_left_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Pilot.first_left_margin
