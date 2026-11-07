import NNH_S1DecodeOk
set_option autoImplicit false
noncomputable section
namespace NNH_S1CodecOk
open Aeneas Aeneas.Std AspisR1 AdapterRw NND_Carrier NNH_Libraries

theorem decode (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation)
 (publicData : Slice U8) (st : C.Statement)
 (success : C.decodeStatement (LIB_Carriers.bytes publicData)=some st) :
 ∃ native,(NNH_CorrectConfiguration.sdk missing env err reserve).op47 publicData=.ok (.Ok native) ∧
 NNH_S1DecodeOk.carrier native=st := NNH_S1DecodeOk.source publicData st success

theorem validate (st : C.Statement) (good : C.validateStatement st=true) :
 NMT_345.validateCall st=.ok (.Ok ()) := (LIBC_S1.valid_iff st).mp good

theorem encode (st : C.Statement) (encoded : RSL.Bytes) (good : C.encodeCandidate st=some encoded) :
 ∃ native,NMT_345.encodeCall (NMT_345.commonValue st).lane_transition.candidate_afterstate=.ok (.Ok native) ∧
 native.val.map NMT_345.byte=encoded := by
 change LIBC_S1.encode st=some encoded at good
 unfold LIBC_S1.encode at good
 cases run : NMT_345.encodeCall (NMT_345.commonValue st).lane_transition.candidate_afterstate with
 | fail e => simp only [run] at good; cases good
 | div => simp only [run] at good; cases good
 | ok reply => cases reply with
   | Err e => simp only [run] at good; cases good
   | Ok native => exact ⟨native,rfl,Option.some.inj good⟩
#print axioms decode
#print axioms validate
#print axioms encode
end NNH_S1CodecOk
