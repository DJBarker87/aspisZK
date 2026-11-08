import NNG_TailReady345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_GuardAssociation345
open Aeneas Aeneas.Std Result NMT_345

theorem source {W : Type} (s : ProofData W) (env : RSL.Env)
 (hd : decodeCall s.publicData=ok (.Ok s.statement))
 (hv : validateCall s.statement=ok (.Ok ()))
 (length : s.proofData.val.length=58295) (route : s.data.val.length=2) :
 NNG_TailReady345.guarded s (s.proofData.val[696]'(by omega)) (s.data.val[1]'(by omega)) env=
 NNG_Phases345.stepProofGuard LIB_Instances.VL LIB_Instances.C
 (NNG_ProjectFrames345.proofData s hd hv)
 (fun p=>NNG_Phases345.stepFirst LIB_Instances.VL LIB_Instances.C NNG_Producer328.producer p env) := by
 have prefixBytes : LIB_Carriers.bytes (NNG_Windows345.window s.proofData 0 688)=
   (LIB_Carriers.bytes s.proofData).take 688 := by
  rw [NNG_Windows345.bytes]
  rfl
 have prefixCompare : ((LIB_Carriers.bytes s.proofData).take 688 != s.candidate.val.map byte)=
   (!decide ((NNG_Windows345.window s.proofData 0 688).val=s.candidate.val)) := by
  rw [← prefixBytes,← NNG_DecoderGraph345.bytes]
  exact NNG_ByteGuards345.unequal _ _
 have tagByte : (LIB_Carriers.bytes s.proofData).getD 696 0=byte (s.proofData.val[696]'(by omega)) := by
  rw [← NNG_DecoderGraph345.bytes]
  exact NNG_ByteGuards345.byte_at _ _ (by omega)
 have lengthCompare : ((LIB_Carriers.bytes s.proofData).length != 58295)=false := by
  rw [NMS_R2N_RSLScalars.bytes_length]
  simp only [length,bne_self_eq_false]
 have guard : NNG_Phases345.proofBad LIB_Instances.VL LIB_Instances.C
    (NNG_ProjectFrames345.proofData s hd hv)=
   (!decide ((NNG_Windows345.window s.proofData 0 688).val=s.candidate.val) ||
    (s.proofData.val[696]'(by omega)) != 2#u8) := by
  change ((LIB_Carriers.bytes s.proofData).length != 58295 ||
    (LIB_Carriers.bytes s.proofData).take 688 != s.candidate.val.map byte ||
    (LIB_Carriers.bytes s.proofData).getD 696 0 != (2 : UInt8)) = _
  rw [lengthCompare,prefixCompare,tagByte,NNG_ByteGuards345.tag]
  rfl
 unfold NNG_Phases345.stepProofGuard
 rw [guard]
 unfold NNG_Phases345.stepFirst
 dsimp only
 rw [← NNG_FirstArgs345.source s hd hv route]
 unfold NNG_TailReady345.guarded
 cases p : !decide ((NNG_Windows345.window s.proofData 0 688).val=s.candidate.val) <;>
  cases t : (s.proofData.val[696]'(by omega)) != 2#u8 <;> rfl
#print axioms source
end AspisR1.NNG_GuardAssociation345
