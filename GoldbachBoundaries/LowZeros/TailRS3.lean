/- Adapted from a pilot built on the zeta project by Mercuri and Mehta
   (Apache-2.0); uses its certified evaluation. -/

module

public import Zeta.Zeros.BuildCertsRS

@[expose] public section

namespace Pilot

open Complex Set Zeta.Certificates

theorem tailRS3 : BatchSpec 78 415227 1000 529115 1000 := by build_batch_rs 160 238

end Pilot
