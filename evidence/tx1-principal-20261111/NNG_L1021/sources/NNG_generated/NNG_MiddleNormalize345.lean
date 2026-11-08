import NNG_Tree345
import NNG_EncoderGraph345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_MiddleNormalize345
open Aeneas Aeneas.Std Result NMT_345 NMT_CallTree NNG_Observed136

def normalized {W : Type} (s : Decoded W) (env : RSL.Env) (next : ProofData W → Code Ret) : Code Ret :=
 NNG_TreeBase345.tryCode (NNG_ValidatorGraph345.native s.statement) fun _=>
 NNG_TreeBase345.tryCode (NNG_EncoderGraph345.native s.statement) fun candidate=>
 NNG_TreeBase345.tryCode
  (NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data (NNG_Calls345.calls env).c10 s.proofAccount)
  (fun proof=>next ⟨⟨s,candidate⟩,proof⟩)

theorem source {W : Type} (s : Decoded W) (env : RSL.Env) (next : ProofData W → Code Ret)
 (events : Event → List RSL.Event) :
 observation NNG_ChildSource345.port events (NNG_TreeBase345.middle (NNG_Calls345.calls env) s next)=
 observation NNG_ChildSource345.port events (normalized s env next) := by
 unfold NNG_TreeBase345.middle normalized NNG_ValidatorGraph345.native NNG_EncoderGraph345.native
 dsimp only [NNG_Calls345.calls]
 cases hv : validateCall s.statement with
 | fail e=>rfl
 | div=>rfl
 | ok v=>
  cases v with
  | Err e=>rfl
  | Ok u=>
   cases u
   unfold commonCall
   cases he : encodeCall (commonValue s.statement).lane_transition.candidate_afterstate with
   | fail e=>rfl
   | div=>rfl
   | ok r=>cases r <;> rfl
#print axioms source
end AspisR1.NNG_MiddleNormalize345
