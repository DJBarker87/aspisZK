import RPz7_FIn_WeightsInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_WeightsTools
open Aeneas Aeneas.Std Result FIn_WeightsExtract
abbrev Q := field.QM31
abbrev Factors := Array (Array (Array Q 4#usize) 5#usize) 5#usize
attribute [local irreducible] weights_new_loop0 weights_new_loop1

theorem source (alpha : Array Q 10#usize) (z : Array circle.SecureCirclePoint 2#usize)
    (points : Array (Array Q 10#usize) 3#usize) (initial middle last : Factors) (q8 q9 : Q)
    (first : state_only_prefix.r0.statement_points alpha=ok points)
    (read8 : Array.index_usize alpha 8#usize=ok q8)
    (read9 : Array.index_usize alpha 9#usize=ok q9)
    (init : Array.repeat 5#usize (Array.repeat 5#usize (Array.repeat 4#usize field.QM31.ZERO))=initial)
    (loop0 : weights_new_loop0 {start:=0#usize,«end»:=3#usize} points initial=ok middle)
    (loop1 : weights_new_loop1 {start:=0#usize,«end»:=2#usize} z middle=ok last) :
    weights_new .S2 alpha z=ok (.Ok (⟨.S2,last,points,Array.make 2#usize [q8,q9]⟩ : Weights)) := by
  unfold weights_new
  rw [first,bind_tc_ok,read8,bind_tc_ok,read9,bind_tc_ok]
  dsimp only
  rw [init,loop0,bind_tc_ok,loop1,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JGo_TX2_WeightsTools
end
