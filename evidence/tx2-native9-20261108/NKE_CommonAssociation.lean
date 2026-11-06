import NKE_CommonEval
import NJU_ResumeRoot
set_option autoImplicit false
noncomputable section
namespace NKE_CommonAssociation
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- Concrete caller G after forward substitution of each child model at its
SAME call arguments. Callee callbacks are AUXILIARY here, never positive-root
hypotheses. Native scope/domain/frame coverage remains a separate gate. -/
theorem source (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H) :
 NKE_FreeReplay.G (NKE_CommonProgram.run wr rr merkle finish d pub proof ck hash none)
  (NJU_CommonObserved.run wr rr merkle finish d pub proof ck hash none).events=
 NKE_FreeReplay.State.done (NJJ_Common.run wr rr merkle finish d pub proof ck hash none) [] := by
 have actual := NKE_FreeReplay.source (NKE_CommonProgram.run wr rr merkle finish d pub proof ck hash none)
 rw [NKE_CommonEval.source,NJU_CommonObserved.source] at actual
 exact actual

/-- The full continuation, including the unmodified frame, agrees after EVERY
entered event prefix, including Rust Err and outer abort/divergence prefixes. -/
theorem prefixes (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H) (n : Nat) :
 NKE_FreeReplay.advance n (NKE_CommonProgram.run wr rr merkle finish d pub proof ck hash none)
  (NJU_CommonObserved.run wr rr merkle finish d pub proof ck hash none).events=
 NKE_FreeReplay.sourcePrefix n (NKE_CommonProgram.run wr rr merkle finish d pub proof ck hash none) := by
 have actual := NKE_FreeReplay.prefixes (NKE_CommonProgram.run wr rr merkle finish d pub proof ck hash none) n
 rw [NKE_CommonEval.source] at actual
 exact actual
#print source
#print prefixes
#print axioms source
#print axioms prefixes
end NKE_CommonAssociation
