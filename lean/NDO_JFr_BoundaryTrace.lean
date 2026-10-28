import NDO_JFr_WordArithmetic
set_option autoImplicit false
namespace AspisR1.JFr_BoundaryTrace
open Aeneas Aeneas.Std Result ControlFlow
open JFr_WordArithmetic
abbrev boundary := AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary_loop
abbrev body := AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary_loop.body

inductive Segment (p : Array Q 28#usize) : Usize → Q → Usize → Q → Prop
  | refl (i : Usize) (x : Q) : Segment p i x i x
  | step {i j stop : Usize} {x c y out : Q}
      (active : i < 28#usize) (read : Array.index_usize p i=ok c)
      (add : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add x c=ok y)
      (inc : i+1#usize=ok j) (tail : Segment p j y stop out) : Segment p i x stop out

theorem append {p : Array Q 28#usize} {i j k : Usize} {x y z : Q}
    (a : Segment p i x j y) (b : Segment p j y k z) : Segment p i x k z := by
  induction a with
  | refl => exact b
  | step active read add inc tail ih => exact .step active read add inc (ih b)

theorem source {p : Array Q 28#usize} {i stop : Usize} {x out : Q}
    (trace : Segment p i x stop out) (done : ¬ stop < 28#usize) :
    boundary p x i=ok out := by
  induction trace with
  | refl i x =>
    unfold boundary AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary_loop loop
    dsimp only
    simp only [body,AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary_loop.body,if_neg done]
  | @step i j stop x c y out active read add inc tail ih =>
    have bodyCall : body p x i=ok (.cont (y,j)) := by
      simp only [body,AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary_loop.body,
        if_pos active,read,add,inc,bind_tc_ok]
    unfold boundary AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary_loop at ih ⊢
    unfold loop
    dsimp only
    dsimp only [body] at bodyCall
    rw [bodyCall]
    exact ih done

#print axioms append
#print axioms source
end AspisR1.JFr_BoundaryTrace
