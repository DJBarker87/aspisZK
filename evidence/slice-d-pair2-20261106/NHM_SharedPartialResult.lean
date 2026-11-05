import NHM_SharedPartialsDomain
set_option autoImplicit false
namespace NHM_SharedPartialResult
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
open NHM_SharedPartials

def canonicalResult : Reply→Prop
 | .Ok a=>∀ x∈a.val,canonE x
 | .Err _=>True

theorem terminal (f : Slice U8) (q : Array NQ 16#usize) (s : State) (r : Reply)
 (h : NHM_SharedPartialsDomain.Inv s) (run : body f q s=ok (.done r)) : canonicalResult r := by
 unfold body at run
 obtain ⟨⟨o,next⟩,hn,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 cases o with
 | none=>cases ControlFlow.done.inj (Result.ok.inj run);exact h.2.2
 | some side=>
  obtain ⟨reply,hr,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  cases reply with
  | Ok x=>
   simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
   obtain ⟨after,ha,run⟩:=Port3_PushFrame.bind_success _ _ _ run
   cases run
  | Err e=>
   simp only [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame,lift,bind_tc_ok] at run
   cases ControlFlow.done.inj (Result.ok.inj run)
   trivial

theorem source (f : Slice U8) (q : Array NQ 16#usize) (out : Cells)
 (run : FIo_Native.weights.shared_partials f q=ok (.Ok out)) : ∀ x∈out.val,canonE x := by
 rw [cohort] at run
 exact NHM_ResultInvariant.stateful (body f q) NHM_SharedPartialsDomain.Inv canonicalResult
  (NHM_SharedPartialsDomain.preserves f q) (terminal f q) 5 _ (.Ok out)
  (NHM_SharedPartialsDomain.all_calls f q).1 run

#print axioms terminal
#print axioms source
end NHM_SharedPartialResult
