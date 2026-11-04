import NEW_LoopMap
set_option autoImplicit false
namespace NEW_ResultMapSyntax
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

theorem pair {A B C D : Type} (f : C → D) (p : A × B) (k : A → B → Result C) :
    resultMap f (let (a,b) := p; k a b) =
      (let (a,b) := p; resultMap f (k a b)) := by cases p; rfl

theorem option {A B C : Type} (f : B → C) (o : Option A) (noneCase : Result B)
    (someCase : A → Result B) :
    resultMap f (match o with | none => noneCase | some a => someCase a) =
      (match o with | none => resultMap f noneCase | some a => resultMap f (someCase a)) := by
  cases o <;> rfl

#print axioms pair
#print axioms option
end NEW_ResultMapSyntax
