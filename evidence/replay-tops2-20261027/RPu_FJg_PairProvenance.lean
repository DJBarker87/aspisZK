import RPu_FJc_PairInactiveTrace
import RPu_FJf_PartialInstalled
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_PairProvenance
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NQ NE)
attribute [local irreducible] FIo_Native.weights.powers
  FIo_Native.weights.Weights.pair_loop1 FIo_Native.weights.shared_partials
  FIo_Native.weights.shared_high
theorem continued (r : core.result.Result Unit FIo_Native.verifier.Error) (u : Unit)
    (h : core.result.Result.Insts.CoreOpsTry.branch r=ok (core.ops.control_flow.ControlFlow.Continue u)) :
    r=.Ok () := by cases r <;> cases h <;> rfl
#print axioms continued
/-- The accepted two-fold native Pair either selected its actual fallback,
or reached the shared calls on the original message and installed self. -/
theorem reached [FIo_Native.Allocation] (self : FIo_Native.weights.Weights)
    (alpha : Slice NE) (f : Slice U8) (kappa out : NE)
    (folds : Slice.len alpha=2#usize)
    (run : FIo_Native.weights.Weights.pair self alpha f kappa=ok (.Ok out)) :
    FIo_Native.weights.shared_two_point_guard self 2#usize=ok false ∨
    ∃ (a0 a1 : NE) (ap0 ap1 : Array NE 4#usize) (common : Array NQ 16#usize)
      (nativeSelf : FIo_Native.weights.Weights) (status : core.result.Result Unit FIo_Native.verifier.Error)
      (partials : Array NE 4#usize) (before after : Array NE 7#usize),
      FIo_Native.weights.shared_two_point_guard self 2#usize=ok true ∧
      Slice.index_usize alpha 0#usize=ok a0 ∧
      FIo_Native.weights.powers 4#usize a0=ok ap0 ∧
      Slice.index_usize alpha 1#usize=ok a1 ∧
      FIo_Native.weights.powers 4#usize a1=ok ap1 ∧
      FIo_Native.weights.Weights.pair_loop1 {start:=0#usize,«end»:=16#usize} self
        (Array.repeat 16#usize FIo_Native.aspis_core.field.QM31.ZERO)=ok (nativeSelf,common) ∧ nativeSelf=self ∧
      FIo_Native.weights.shared_partials f common=ok (.Ok partials) ∧
      FIo_Native.weights.shared_high partials nativeSelf ap0 ap1 before=ok (status,after) ∧ status=.Ok () := by
  unfold FIo_Native.weights.Weights.pair at run
  simp only [folds,ite_true,show ¬(2#usize=1#usize) from by decide,ite_false] at run
  repeat' first
  | (solve | cases run)
  | uncase_result
  | head_reduce run
  | split at run
  all_goals
    first
    | (solve | left; simp_all only [Bool.not_eq_true])
    | right
      obtain ⟨a1,h1,hp1⟩ := Port3_PushFrame.bind_success
        (Slice.index_usize alpha 1#usize) (fun a=>FIo_Native.weights.powers 4#usize a) _ (by assumption)
      refine ⟨_,a1,_,_,_,_,_,_,_,_,by simp_all only [Bool.not_eq_true],by assumption,by assumption,h1,hp1,
        by assumption,?_,by assumption,by assumption,?_⟩
      · exact FJc_SharedSelf.value self _ _ _ _ (by assumption)
      · exact continued _ _ (by assumption)
#print axioms reached
end AspisR1.FJg_PairProvenance
end
