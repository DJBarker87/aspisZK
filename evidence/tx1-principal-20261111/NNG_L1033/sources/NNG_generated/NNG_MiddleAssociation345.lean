import NNG_MiddleNormalize345
import NNG_EncodeAssociation345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_MiddleAssociation345
open Aeneas Aeneas.Std Result NMT_345 NMT_CallTree NNG_Observed136

theorem source {W : Type} (s : Decoded W) (env : RSL.Env)
 (hd : decodeCall s.publicData=ok (.Ok s.statement))
 (next : ProofData W → Code Ret)
 (tail : NNG_EncodeAssociation345.LogicalProof → RSL.Obs (Except RSL.ProgramError RSL.Bytes))
 (later : ∀ (hv : validateCall s.statement=ok (.Ok ())) candidate proof,
  observation NNG_ChildSource345.port (NNG_Events345.events env) (next ⟨⟨s,candidate⟩,proof⟩)=
   tail (NNG_ProjectFrames345.proofData ⟨⟨s,candidate⟩,proof⟩ hd hv)) :
 observation NNG_ChildSource345.port (NNG_Events345.events env)
 (NNG_TreeBase345.middle (NNG_Calls345.calls env) s next)=
 NNG_Phases345.stepValidate LIB_Instances.VL LIB_Instances.C
 (NNG_ProjectFrames345.decoded s hd) fun v=>
  NNG_Phases345.stepEncode LIB_Instances.VL LIB_Instances.C v fun c=>
   NNG_Phases345.stepProofData LIB_Instances.VL LIB_Instances.C (fun _=>true) c tail := by
 rw [NNG_MiddleNormalize345.source]
 unfold NNG_MiddleNormalize345.normalized NNG_ValidatorGraph345.native NNG_Phases345.stepValidate
 change _=(if h : LIBC_S1.valid s.statement=true then _ else _)
 unfold LIBC_S1.valid
 rw [NMT_R2_ValidatorTotal.emitted]
 cases hr : NMT_R2_ValidatorTotal.fresh s.statement with
 | Err e=>rfl
 | Ok u=>
  cases u
  have hv : validateCall s.statement=ok (.Ok ()) := by
   rw [NMT_R2_ValidatorTotal.emitted,hr]
  exact NNG_EncodeAssociation345.source s env hd hv next tail (later hv)
#print axioms source
end AspisR1.NNG_MiddleAssociation345
