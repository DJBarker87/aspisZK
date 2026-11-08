import NNG_ProjectFrames345
import NNG_PrefixEquations345
import NNG_TryAssociation345
import NNG_EncoderGraph345
import NNG_Events345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_EncodeAssociation345
open Aeneas Aeneas.Std Result NMT_345 NMT_CallTree NNG_Observed136
abbrev LogicalProof := NNG_Phases345.ProofData LIB_Instances.VL LIB_Instances.C

theorem source {W : Type} (s : Decoded W) (env : RSL.Env)
 (hd : decodeCall s.publicData=ok (.Ok s.statement))
 (hv : validateCall s.statement=ok (.Ok ()))
 (next : ProofData W → Code Ret)
 (tail : LogicalProof → RSL.Obs (Except RSL.ProgramError RSL.Bytes))
 (later : ∀ candidate proof,
  observation NNG_ChildSource345.port (NNG_Events345.events env) (next ⟨⟨s,candidate⟩,proof⟩)=
   tail (NNG_ProjectFrames345.proofData ⟨⟨s,candidate⟩,proof⟩ hd hv)) :
 observation NNG_ChildSource345.port (NNG_Events345.events env)
 (NNG_TreeBase345.tryCode (NNG_EncoderGraph345.native s.statement) fun candidate=>
  NNG_TreeBase345.tryCode
  (NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data (NNG_Calls345.calls env).c10 s.proofAccount)
  (fun proof=>next ⟨⟨s,candidate⟩,proof⟩))=
 NNG_Phases345.stepEncode LIB_Instances.VL LIB_Instances.C
 (NNG_ProjectFrames345.validated s hd hv) fun c=>
  NNG_Phases345.stepProofData LIB_Instances.VL LIB_Instances.C (fun _=>true) c tail := by
 unfold NNG_EncoderGraph345.native NNG_Phases345.stepEncode
 change _ = (match LIBC_S1.encode s.statement with | none=>_ | some bytes=>_)
 unfold LIBC_S1.encode
 rw [NMT_R2_EncoderTotal.source]
 cases he : NMT_R2_EncoderTotal.value (commonValue s.statement).lane_transition.candidate_afterstate with
 | Err e=>rfl
 | Ok candidate=>
  change observation _ _ (NNG_TreeBase345.tryCode
    (NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data (NNG_Calls345.calls env).c10 s.proofAccount)
    (fun proof=>next ⟨⟨s,candidate⟩,proof⟩)) = _
  unfold NNG_Phases345.stepProofData
  rw [← NNG_PrefixEquations345.data s.proofAccount env]
  apply NNG_TryAssociation345.source (fun b : Slice U8=>LIB_Carriers.bytes b)
  intro proof _
  exact later candidate proof
#print axioms source
end AspisR1.NNG_EncodeAssociation345
