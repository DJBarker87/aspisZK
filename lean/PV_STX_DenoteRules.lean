import PV_STX_Code
set_option autoImplicit false
noncomputable section
namespace PV_STX_DenoteRules
open Aeneas Aeneas.Std PV_STX_Code
variable {Op : Type → Type 1} {A B X Y : Type}
variable (f : {T : Type} → Op T → Result T)
theorem pure_rule (a : A) : denote f (pure a : Code Op A) = .ok a := rfl
theorem bind_rule (c : Code Op A) (k : A → Code Op B) :
    denote f (c >>= k) = (do let a ← denote f c; denote f (k a)) := by
  change Aeneas.Std.bind (denote f c) (fun a => denote f (k a)) = _
  cases denote f c <;> rfl
theorem result_rule (r : Result A) : denote f (Code.result r) = r := rfl
theorem call_rule (op : Op A) : denote f (Code.call op) = f op := rfl
theorem if_rule (p : Prop) [Decidable p] (a b : Code Op A) :
    denote f (if p then a else b) = if p then denote f a else denote f b := by
  by_cases h : p <;> simp only [h,if_true,if_false]
theorem pair_rule (p : X × Y) (k : X → Y → Code Op A) :
    denote f (match p with | (x,y) => k x y) =
      match p with | (x,y) => denote f (k x y) := by cases p; rfl
theorem cf_rule (c : core.ops.control_flow.ControlFlow X Y)
    (left : X → Code Op A) (right : Y → Code Op A) :
    denote f (match c with | .Break x => left x | .Continue y => right y) =
      match c with | .Break x => denote f (left x) | .Continue y => denote f (right y) := by
  cases c <;> rfl
theorem loop_rule (body : X → Code Op (ControlFlow X A)) (x : X) :
    denote f (Code.loop body x) = Aeneas.Std.loop (fun t => denote f (body t)) x := rfl
#print axioms pure_rule
#print axioms bind_rule
#print axioms result_rule
#print axioms call_rule
#print axioms if_rule
#print axioms pair_rule
#print axioms cf_rule
#print axioms loop_rule
end PV_STX_DenoteRules
