import NKE_EventTactic
set_option autoImplicit false
noncomputable section
namespace NKE_CommonCalls
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- Complete source call equations, all nine event constructors and every
Result. These are SAME-occurrence source facts, not native certificates. -/
def Clause (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (hash : H) : Event → Prop
 | .resume ck proof pub reply => reply=NJJ_Common.resume wr d ck proof pub .S2 hash
 | .powers gamma reply => reply=NHT_PacketOps.powers 29#usize gamma
 | .inactive bytes reply => reply=NJC_ClosedCalls.inactive bytes
 | .merkle proof p root reply => reply=merkle d proof p root 1#usize hash
 | .geometry queries next reply => reply=NJC_ClosedCalls.geometry queries next 22#usize
 | .pending weights reply => reply=NJJ_Common.pending rr weights
 | .query proof p a g geometry pending reply =>
   reply=NJJ_Common.query proof p a g none geometry pending 22#usize
 | .flush pending weights reply => reply=Port3_FlushInstall.flush pending weights
 | .finish v p a reply => reply=finish v p a none
#print axioms Clause
end NKE_CommonCalls
