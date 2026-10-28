import NDO_JFr_IndexArithmetic
set_option autoImplicit false
namespace AspisR1.JFr_HornerTrace
open Aeneas Aeneas.Std Result ControlFlow
open JFr_WordArithmetic
abbrev value := AspisR1SemanticCallExtraction.r1_semantic.semantic_value_loop
inductive Segment (p : Array Q 28#usize) (a : Array Q 10#usize) (r : Usize) : Usize → Q → Usize → Q → Prop
  | refl (i : Usize) (x : Q) : Segment p a r i x i x
  | step {i j stop : Usize} {x alpha c prod y out : Q}
      (active : i > 0#usize) (dec : i-1#usize=ok j)
      (challenge : Array.index_usize a r=ok alpha)
      (mul : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul x alpha=ok prod)
      (read : Array.index_usize p j=ok c)
      (add : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add prod c=ok y)
      (tail : Segment p a r j y stop out) : Segment p a r i x stop out

theorem append {p : Array Q 28#usize} {a : Array Q 10#usize} {r i j k : Usize} {x y z : Q}
    (u : Segment p a r i x j y) (v : Segment p a r j y k z) : Segment p a r i x k z := by
  induction u with
  | refl => exact v
  | step active dec challenge mul read add tail ih => exact .step active dec challenge mul read add (ih v)

theorem source {p : Array Q 28#usize} {a : Array Q 10#usize} {r i stop : Usize} {x out : Q}
    (trace : Segment p a r i x stop out) (done : ¬ stop > 0#usize) :
    value p a r i x=ok out := by
  induction trace with
  | refl i x =>
    unfold value AspisR1SemanticCallExtraction.r1_semantic.semantic_value_loop loop
    dsimp only
    simp only [AspisR1SemanticCallExtraction.r1_semantic.semantic_value_loop.body,if_neg done]
  | @step i j stop x alpha c prod y out active dec challenge mul read add tail ih =>
    have bodyCall : AspisR1SemanticCallExtraction.r1_semantic.semantic_value_loop.body p a r i x=ok (.cont (j,y)) := by
      simp only [AspisR1SemanticCallExtraction.r1_semantic.semantic_value_loop.body,
        if_pos active,dec,challenge,mul,read,add,bind_tc_ok]
    unfold value AspisR1SemanticCallExtraction.r1_semantic.semantic_value_loop at ih ⊢
    unfold loop
    dsimp only
    rw [bodyCall]
    exact ih done

#print axioms append
#print axioms source
end AspisR1.JFr_HornerTrace
