import NNH_Stage1Cut
import NNH_S1CodecOk
set_option autoImplicit false
noncomputable section
namespace NNH_Stage1PublicDomain
open Aeneas Aeneas.Std AspisR1 RSL NNH_Libraries

theorem produce (a : TX1_345.Args) (p pub ck : OwnedAccount) (saved : Bytes) (env : Env)
 (packet : NNH_Stage1Cut.Packet a p pub ck saved env) :
 VL.publicDom (C.semanticPublic packet.statement) ∧
 NMT_345.validateCall packet.statement=.ok (.Ok ()) ∧
 ∃ native,NMT_345.encodeCall (NMT_345.commonValue packet.statement).lane_transition.candidate_afterstate=.ok (.Ok native) ∧
 native.val.map NMT_345.byte=packet.candidate := by
 exact ⟨LIB_S1.validated_public packet.statement packet.valid,
  NNH_S1CodecOk.validate packet.statement packet.valid,
  NNH_S1CodecOk.encode packet.statement packet.candidate packet.encode⟩
#print axioms produce
end NNH_Stage1PublicDomain
