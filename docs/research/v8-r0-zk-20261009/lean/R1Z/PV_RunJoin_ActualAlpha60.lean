import R1Z.PV_RunJoin_ActualRun59
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ActualAlpha60
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_NativeControl55 (Phase)
open PV_RunJoin_ActualData59
open ProverCommitValueRange47 (embed)
open AspisR1.ExtractedCurrentQM31Exact (decode)
variable [ExternalTypes] [ExternalFuns]

theorem stored (p : Phase) :
    (fun i => embed (ProverCommitSuccessorPoint49.decoded (data p).p i))=
      R0Z.HonestView.alpha (data p).ch := by
  funext i
  have hi : i.val<10 := i.isLt
  have hiword : i.val<(10#usize).val := hi
  have hlen : i.val<p.sem.alpha.val.length := by rw [p.sem.alpha.property];exact hi
  simp only [data,challenges,R0Z.HonestView.alpha,semantic,
    ProverCommitSuccessorPoint49.decoded,PV_RunJoin_SemanticMaterialInputs50.alpha,
    PV_RunJoin_SemanticArray50.raw,dif_pos hiword,Option.getD_some,
    show ¬15+i.val=0 from by omega,show ¬15+i.val=1 from by omega,
    show ¬15+i.val=2 from by omega,show ¬15+i.val<13 from by omega,
    show ¬15+i.val=13 from by omega,show ¬15+i.val=14 from by omega,
    if_false,Nat.add_sub_cancel_left,List.getElem?_eq_getElem hlen]

#print axioms stored
end R1Z.PV_RunJoin_ActualAlpha60
