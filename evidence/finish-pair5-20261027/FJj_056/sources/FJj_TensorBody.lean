import FJj_TensorCell
set_option autoImplicit false
namespace AspisR1.FJj_TensorBody
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NQ)
open FJa_ReverseStep (Rev next)

theorem cont (self : FIo_Native.weights.Weights) (k n d j : Usize)
    (iter cursor : Rev) (input : Slice NQ)
    (hn : next iter=ok (some j,cursor))
    (r : ControlFlow (Rev × Slice NQ) (FIo_Native.weights.Weights × Slice NQ))
    (run : FIo_Native.weights.Weights.tensor_loop0_loop0.body self k n d iter input=ok r) :
    ∃ out : Slice NQ,r=.cont (cursor,out) := by
  unfold next at hn
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body at run
  rw [hn] at run
  simp only [bind_tc_ok] at run
  repeat' first | (solve | cases run) | uncase_result | head_reduce run | split at run
  exact ⟨_,(Result.ok.inj run).symm⟩

theorem done (self : FIo_Native.weights.Weights) (k n d : Usize)
    (iter cursor : Rev) (input : Slice NQ)
    (hn : next iter=ok (none,cursor)) :
    FIo_Native.weights.Weights.tensor_loop0_loop0.body self k n d iter input=ok (.done (self,input)) := by
  unfold next at hn
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body
  rw [hn]
  rfl
#print axioms cont
#print axioms done
end AspisR1.FJj_TensorBody
