import NNG_LogicalProjection345
import NNG_ReturnSize345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_CutGuards345
open Aeneas Aeneas.Std RSL NNG_Phases345

def bad (b candidate : Bytes) : Bool :=
 b.length != PROOF_ACCOUNT_BYTES || b.take AFTERSTATE_BYTES != candidate ||
 b.getD (AFTERSTATE_BYTES+8) 0 != TX1_345.S2_TAG

theorem proof_guard (b candidate : Bytes) : bad (NNG_Cut345.cut b) candidate=bad b candidate := by
 by_cases fit : b.length≤Usize.max
 · rw [NNG_Cut345.fixed b fit]
 · have maximum : 58295≤Usize.max := by scalar_tac
   have original : (b.length !=58295)=true := bne_iff_ne.mpr (by omega)
   have projected : ((NNG_Cut345.cut b).length !=58295)=true :=
    (NNG_Cut345.width b 58295 (by decide) maximum).trans original
   change ((NNG_Cut345.cut b).length !=58295 || _ || _)= (b.length !=58295 || _ || _)
   rw [original,projected]
   rfl
#print axioms proof_guard

theorem frame (s : ProofData NNG_LogicalProjection345.V NNG_LogicalProjection345.C) :
 proofBad NNG_LogicalProjection345.V NNG_LogicalProjection345.C (NNG_LogicalProjection345.proofData s)=
 proofBad NNG_LogicalProjection345.V NNG_LogicalProjection345.C s :=
 proof_guard s.proofData s.candidate
#print axioms frame

theorem returned (checkpoint bytes : Bytes) (size : bytes.length=1768) :
 stepReturn (NNG_Cut345.cut checkpoint).length bytes=stepReturn checkpoint.length bytes := by
 have width := NNG_Cut345.width checkpoint 1768 (by decide) (by scalar_tac)
 have comparison : (1768 !=(NNG_Cut345.cut checkpoint).length)=(1768 !=checkpoint.length) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [bne_iff_ne,ne_comm] using Bool.eq_iff_iff.mp width
 unfold stepReturn
 rw [size,comparison]
#print axioms returned
end AspisR1.NNG_CutGuards345
