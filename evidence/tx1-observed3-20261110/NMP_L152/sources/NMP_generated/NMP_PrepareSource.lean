import NMP_PrepareSuffix0
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_PrepareSuffix
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted NMP_PrepareSteps
/-- Full normalized Result equals the actual E002 emitted prepare, with std
map_err interpreted by its complete library law. No input-success premise. -/
theorem source {H W : Type} (c : Calls) (s : Parent H W) :
 f0 c s = prepare (standard c) s := by
 unfold f0 prepare standard NMP_prepare.verifier.candidate.prepare
 simp only [NMP_EmittedConstants.logical_semantic,NMP_EmittedConstants.logical_y1,
  NMP_EmittedConstants.off_semantic,NMP_EmittedConstants.off_y1,
  NMP_EmittedConstants.off_inactive,NMP_EmittedConstants.total,
  lift,NMP_DirectBind.ok,bind_tc_ok]
 apply NMT_CallTree.result_congr
 intro r
 cases r with
 | Err e => rfl
 | Ok logical =>
  unfold f1
  apply NMT_CallTree.result_congr
  intro pair
  rcases pair with ⟨⟨semantic,y1⟩,back⟩
  unfold f2
  apply NMT_CallTree.result_congr
  intro src
  apply NMT_CallTree.result_congr
  intro pair
  rcases pair with ⟨r,after⟩
  cases r with
  | Err e => rfl
  | Ok u =>
   unfold f3
   apply NMT_CallTree.result_congr
   intro src
   apply NMT_CallTree.result_congr
   intro pair
   rcases pair with ⟨r,afterY1⟩
   cases r with
   | Err e => rfl
   | Ok u =>
    apply NMT_CallTree.result_congr
    intro fullSemantic
    apply NMT_CallTree.result_congr
    intro fullY1
    unfold f4
    apply NMT_CallTree.result_congr
    intro r
    cases r with
    | Err e => rfl
    | Ok v =>
     unfold f5
     apply NMT_CallTree.result_congr
     intro r
     cases r with
     | Err e => rfl
     | Ok sem => rfl
/-- Exact fresh-body erasure, including the scratch returned on Rust Err and
all outer stopped arms. Child and physical-effect installation remains separate. -/
theorem emitted {H W : Type} (c : Calls) (s : Parent H W) :
 NMT_CallTree.erase (NMP_PrepareSteps.body c s) = prepare (standard c) s :=
 (fold0 c s).trans (source c s)
#print axioms source
#print axioms emitted
end AspisR1.NMP_PrepareSuffix
