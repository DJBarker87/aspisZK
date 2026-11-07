import LIBC_Bytes
import LIB_VCarriers
import NHF_ViewInstalled
set_option autoImplicit false
noncomputable section
namespace LIBC_WideView
open Aeneas Aeneas.Std Result RSL
abbrev View := LIB_VCarriers.View
abbrev VErr := LIB_VCarriers.VErr
def error : AspisR1SelectedWideViewV1.verifier.Error → VErr
 | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
 | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
 | .Checkpoint => .Checkpoint | .Allocation => .Allocation
def port (r : core.result.Result AspisR1SelectedWideViewV1.verifier.View
 AspisR1SelectedWideViewV1.verifier.Error) : Except VErr View := match r with
 | .Ok v => .ok (AspisR1SelectedWideViewV1.preparedView v)
 | .Err e => .error (error e)
/-- NHF original prepare-caller domain, verbatim dimensions; all byte values. -/
def Domain (a : Bytes × Bytes × Bytes) : Prop :=
 a.1.length=57607 ∧ a.2.1.length=13831 ∧ a.2.2.length=928
def value (a : Bytes × Bytes × Bytes) (_ : Env) : Except VErr View :=
 if h : 10055 ≤ (LIBC_Bytes.raw a.1).val.length then
  port (AspisR1.NHF_ViewResult.model (LIBC_Bytes.raw a.1)
   (LIBC_Bytes.raw a.2.1) (LIBC_Bytes.raw a.2.2) h)
 else .error .Parse
def child : Child (Bytes × Bytes × Bytes) (Except VErr View) :=
 LIB_Carriers.ofFn Domain value (fun _ _ => [])
theorem proof_bound (a : Bytes × Bytes × Bytes) (h : Domain a) :
 10055 ≤ (LIBC_Bytes.raw a.1).val.length := by
 have b : a.1.length ≤ Usize.max := by rw [h.1];scalar_tac
 rw [LIBC_Bytes.raw_length _ b,h.1]
 omega
theorem model_port (a : Bytes × Bytes × Bytes) (env : Env) (h : Domain a) :
 (do let r ← AspisR1SelectedWideViewV1.verifier.candidate.wide_view
       (LIBC_Bytes.raw a.1) (LIBC_Bytes.raw a.2.1) (LIBC_Bytes.raw a.2.2)
     ok (port r)) = ok (value a env) := by
 rw [AspisR1.NHF_ViewResult.result _ _ _ (proof_bound a h),bind_tc_ok]
 simp only [value,dif_pos (proof_bound a h)]
theorem returns (a : Bytes × Bytes × Bytes) (env : Env) :
 NND_Returned.Returns (child.law a) env (value a env) := LIB_Carriers.ofFn_returns _ _ _ a env
theorem exact (a : Bytes × Bytes × Bytes) (env : Env) (o : Obs (Except VErr View)) :
 child.law a env o ↔ o = ⟨.ret (value a env),[]⟩ := Iff.rfl
/-- Separate emitted-copy carrier law; every returned borrowed field remains
on the same byte backing, including semantic/y1 and the inactive word. -/
theorem emitted_copy (v : AspisR1SelectedWideViewV1.verifier.View) :
 AspisR1CurrentCaller.InstalledPreparation.retainedView
  (AspisR1CurrentCaller.InstalledPreparation.selectedView v) =
 AspisR1SelectedWideViewV1.preparedView v :=
 AspisR1CurrentCaller.InstalledPreparation.retained_selected_view v
theorem semantic_bytes (v : AspisR1SelectedWideViewV1.verifier.View) :
 LIB_VCarriers.viewSemantic (AspisR1SelectedWideViewV1.preparedView v) =
 LIB_Carriers.bytes v.semantic := rfl
theorem native_arguments (proof semantic y1 : Slice U8) :
 (LIBC_Bytes.raw (LIB_Carriers.bytes proof),LIBC_Bytes.raw (LIB_Carriers.bytes semantic),
  LIBC_Bytes.raw (LIB_Carriers.bytes y1)) = (proof,semantic,y1) := by
 rw [LIBC_Bytes.from_native,LIBC_Bytes.from_native,LIBC_Bytes.from_native]
#print axioms proof_bound
#print axioms model_port
#print axioms returns
#print axioms exact
#print axioms emitted_copy
#print axioms semantic_bytes
#print axioms native_arguments
end LIBC_WideView
