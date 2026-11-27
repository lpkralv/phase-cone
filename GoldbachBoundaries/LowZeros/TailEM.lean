/- Adapted from a pilot built on the zeta project by Mercuri and Mehta
   (Apache-2.0); uses its certified evaluation. -/

module

public import Zeta.Zeros.BuildCerts

@[expose] public section

namespace Pilot

open Complex Set Zeta.Certificates

theorem tailEM : BatchSpec 48 32500 1000 149500 1000 := by build_batch 4 52

end Pilot
