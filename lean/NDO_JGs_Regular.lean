import NDO_JGs_K4
import NDO_JGs_RegularForward
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_Regular
open Aeneas Aeneas.Std Result
/-- Constructed forward return of all three native regular parts, in source order. -/
theorem source : @FIo_Native.weights.process_regular_kinds (FIo_Install.allocation (.Ok ()))
    JGq_PairShape.w true JGq_PairShape.alpha JGq_PairShape.f 2#usize 64#usize
    JGq_Powers0.a4 JGq_Powers1.a4 JGq_PairShape.scratch JGq_PairPrefix.initial=
      ok (.Ok (),JGs_K4.scratch,JGs_K4.parts) := by
  letI := FIo_Install.allocation (.Ok ())
  exact JGs_RegularForward.source JGq_PairShape.w JGq_PairShape.alpha JGq_PairShape.f
    2#usize 64#usize JGq_Powers0.a4 JGq_Powers1.a4
    JGq_PairShape.scratch JGs_K1.scratch JGs_K3.scratch JGs_K4.scratch
    JGq_PairPrefix.initial JGs_K1.parts JGs_K3.parts JGs_K4.parts
    JGs_K1.source JGs_K3.source JGs_K4.source
#print axioms source
end AspisR1.JGs_Regular
end
