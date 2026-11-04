import Aeneas
import JFv_RawExtractedSemanticCallOpsV20
set_option autoImplicit false
namespace NEW_LoopMap
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

def flowMap {S A B : Type} (f : A → B) : ControlFlow S A → ControlFlow S B
 | .cont s => .cont s
 | .done a => .done (f a)

def bodyMap {S A B : Type} (body : S → Result (ControlFlow S A)) (f : A → B)
    (s : S) : Result (ControlFlow S B) := resultMap (flowMap f) (body s)

theorem map_ok {A B : Type} (f : A → B) (a : A) : resultMap f (ok a)=ok (f a) := rfl
theorem map_fail {A B : Type} (f : A → B) (e : Error) : resultMap f (fail e)=fail e := rfl
theorem map_div {A B : Type} (f : A → B) : resultMap f div=div := rfl

/-- A defined native loop result follows the mapped loop with the SAME
continuation state. Failure is retained; no termination or output premise. -/
theorem defined_result {S A B : Type} (body : S → Result (ControlFlow S A)) (f : A → B)
    (s : S) : loop body s=div ∨ resultMap f (loop body s)=loop (bodyMap body f) s := by
  have all : ∀ s, loop body s=div ∨ resultMap f (loop body s)=loop (bodyMap body f) s := by
    apply loop.fixpoint_induct body (fun rec =>
      ∀ s, rec s=div ∨ resultMap f (rec s)=loop (bodyMap body f) s)
    · refine Lean.Order.admissible_pi_apply
        (fun x (r : Result A) => r=div ∨ resultMap f r=loop (bodyMap body f) x) ?_
      intro x
      apply Lean.Order.admissible_flatOrder
      exact Or.inl rfl
    · intro rec ih x
      rw [loop.eq_def]
      cases hb : body x with
      | div => simp only [bodyMap,hb,map_div] <;> exact Or.inl True.intro
      | fail e => simp only [bodyMap,hb,map_fail] <;> exact Or.inr True.intro
      | ok c =>
        cases c with
        | done a => simp only [bodyMap,hb,map_ok,flowMap] <;> exact Or.inr True.intro
        | cont next => simpa only [bodyMap,hb,map_ok,flowMap] using ih next
  exact all s

theorem body_inverse {S A B : Type} (body : S → Result (ControlFlow S A))
    (f : A → B) (g : B → A) (back : ∀ a, g (f a)=a) :
    bodyMap (bodyMap body f) g = body := by
  funext s
  cases h : body s with
  | div => simp only [bodyMap,h,map_div]
  | fail e => simp only [bodyMap,h,map_fail]
  | ok c => cases c <;> simp only [bodyMap,h,map_ok,flowMap,back]

theorem map_inverse {A B : Type} (f : A → B) (g : B → A)
    (back : ∀ b, f (g b)=b) (r : Result B) : resultMap f (resultMap g r)=r := by
  cases r <;> simp only [map_ok,map_fail,map_div,back]

/-- Full partial Result transport through a lossless nominal return map.
Both loop state and cont transitions are identical. Divergence and every
failure are preserved using fixpoint induction in BOTH directions. -/
theorem complete {S A B : Type} (body : S → Result (ControlFlow S A))
    (f : A → B) (g : B → A) (gf : ∀ a, g (f a)=a) (fg : ∀ b, f (g b)=b)
    (s : S) : resultMap f (loop body s)=loop (bodyMap body f) s := by
  have forward := defined_result body f s
  have backward := defined_result (bodyMap body f) g s
  rw [body_inverse body f g gf] at backward
  rcases forward with nativeDiv | done
  · rcases backward with modelDiv | done
    · rw [nativeDiv,modelDiv]; rfl
    · have same := congrArg (resultMap f) done
      simpa only [map_inverse f g fg] using same.symm
  · exact done

#print axioms map_ok
#print axioms map_fail
#print axioms map_div
#print axioms defined_result
#print axioms body_inverse
#print axioms map_inverse
#print axioms complete
end NEW_LoopMap
