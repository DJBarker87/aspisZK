import NKI_AppendCut
import NKI_DigestTargets
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_TargetAssociation
open Aeneas Aeneas.Std Result
open NJX_DigestCohort (D dcells)
theorem source {d : D} {side : Bool} (p : NKI_DigestTargets.Packet d side) :
 NKI_DigestTargets.cells p=NKI_AppendCut.targets side (dcells d) p.last := by
 funext i
 cases side with
 | true=>simp only [NKI_DigestTargets.cells,NKI_AppendCut.targets,true_and]
 | false=>
  have h : p.last=dcells d 7 := p.call
  simp only [NKI_DigestTargets.cells,NKI_AppendCut.targets,Bool.false_eq_true,false_and,if_false]
  split
  · next hi=>subst i;exact h
  · rfl
#print axioms source
end AspisR1.NKI_TargetAssociation
end
