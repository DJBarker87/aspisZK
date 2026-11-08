import NNG_LogicalProjection345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ProjectionBind345
open RSL NNG_Obs345 NNG_Pure345

theorem cloned_map {A B D : Type} (f : A → B) (x : Except ProgramError A)
 (next : B → Obs (Except ProgramError D)) :
 tryObs (cloned true (x.map f)) next=tryObs (cloned true x) (fun a=>next (f a)) := by
 cases x with
 | ok a=>rfl
 | error e=>cases e.cloneAllocates <;> rfl
#print axioms cloned_map

theorem allocation (reached : Bool) : allocationIf reached true=silent (.ok ()) := by
 cases reached <;> rfl
#print axioms allocation
end AspisR1.NNG_ProjectionBind345
