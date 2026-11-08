import NNG_GuardAssociation345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_TailAssociation345
open Aeneas Aeneas.Std Result NMT_345 NMT_CallTree NNG_Observed136

theorem source {W : Type} (s : ProofData W) (env : RSL.Env)
 (hd : decodeCall s.publicData=ok (.Ok s.statement))
 (hv : validateCall s.statement=ok (.Ok ()))
 (route : s.data.val.length=2) :
 observation NNG_ChildSource345.port (NNG_Events345.events env)
 (NNG_TreeTail345.bounds (NNG_Calls345.calls env) s)=
 NNG_Phases345.stepProofGuard LIB_Instances.VL LIB_Instances.C
 (NNG_ProjectFrames345.proofData s hd hv)
 (fun p=>NNG_Phases345.stepFirst LIB_Instances.VL LIB_Instances.C NNG_Producer328.producer p env) := by
 by_cases length : s.proofData.val.length=58295
 · exact (NNG_TailReady345.source s env length route).trans
    (NNG_GuardAssociation345.source s env hd hv length route)
 · rw [NNG_BoundsAssociation345.source]
   have native : (Slice.len s.proofData != 58295#usize)=true := by
    rw [NNG_ReturnAssociation345.compare]
    change (s.proofData.val.length != 58295)=true
    simp [length]
   have bad : NNG_Phases345.proofBad LIB_Instances.VL LIB_Instances.C
      (NNG_ProjectFrames345.proofData s hd hv)=true := by
    change ((LIB_Carriers.bytes s.proofData).length != 58295 || _ || _)=true
    rw [NMS_R2N_RSLScalars.bytes_length]
    simp [length]
   unfold NNG_TreeTail345.tail
   rw [if_pos native]
   unfold NNG_Phases345.stepProofGuard
   rw [bad]
   rfl
#print axioms source
end AspisR1.NNG_TailAssociation345
