/- Adapted from a pilot built on the zeta project by Mercuri and Mehta
   (Apache-2.0); uses its certified evaluation. -/

module

public import Zeta.Zeros.BuildCertsRS

@[expose] public section

namespace Pilot

open Complex Set Zeta.Certificates

theorem tailRS1 : BatchSpec 80 149500 1000 290679 1000 := by build_batch_rs 0 80

end Pilot
