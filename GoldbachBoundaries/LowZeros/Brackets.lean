/- Adapted from a pilot built on the zeta project by Mercuri and Mehta
   (Apache-2.0); uses its certified evaluation. -/

module

public import Zeta.Zeros.BuildCerts

@[expose] public section

namespace Pilot

open Complex Set Zeta.Certificates

theorem bracket1 : BatchSpec 1 14134725141734693790457251983562 (10^30) 14134725141734693790457251983563 (10^30) :=
  by build_batch 0 1

theorem bracket2 : BatchSpec 1 21022039638771554992628479593896 (10^30) 21022039638771554992628479593897 (10^30) :=
  by build_batch 1 2

theorem bracket3 : BatchSpec 1 25010857580145688763213790992562 (10^30) 25010857580145688763213790992563 (10^30) :=
  by build_batch 2 3

theorem bracket4 : BatchSpec 1 30424876125859513210311897530584 (10^30) 30424876125859513210311897530585 (10^30) :=
  by build_batch 3 4

end Pilot

#print axioms Pilot.bracket1
