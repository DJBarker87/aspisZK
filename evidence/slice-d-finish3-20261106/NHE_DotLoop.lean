import NHE_DotBody
set_option autoImplicit false
namespace NHE_DotLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1 NHE_DotBody

theorem decreases (bytes : Slice U8) (weights : Slice NQ) (s n : State)
 (run : body bytes weights s=ok (.cont n)) : weights.val.length-n.2.val<weights.val.length-s.2.val := by
 unfold body at run
 split at run
 · rename_i active
   obtain ⟨value,hv,rest⟩ := Port3_PushFrame.bind_success _ _ _ run
   obtain ⟨scalar,hq,rest⟩ := Port3_PushFrame.bind_success _ _ _ rest
   obtain ⟨pair,hp,rest⟩ := Port3_PushFrame.bind_success _ _ _ rest
   rcases pair with ⟨reply,dot⟩
   cases reply with
   | Err u => cases u;cases rest
   | Ok u =>
    cases u
    obtain ⟨j,hj,rest⟩ := Port3_PushFrame.bind_success _ _ _ rest
    have eq : (dot,j)=n := ControlFlow.cont.inj (Result.ok.inj rest)
    have index := congrArg Prod.snd eq
    have value := UScalar.add_equiv s.2 1#usize
    rw [hj] at value
    have plus : j.val=s.2.val+1 := value.2.1
    change s.2.val<weights.val.length at active
    rw [←index]
    change weights.val.length-j.val<weights.val.length-s.2.val
    omega
 · cases run

theorem cohort (bytes : Slice U8) (weights : Slice NQ) (size : weights.val.length≤64) (s : State) :
 FIo_FieldBridge.map rm (loop (body bytes weights) s)=
 AspisR1FinishRelationCurrent.verifier.finish_query_dot_loop ops bytes
  (SAG_DotAdapter.mapSlice NHE_DotRead.finishQ weights) (sm s).1 (sm s).2 :=
 NHE_LoopMap.finite (body bytes weights)
  (fun t=>AspisR1FinishRelationCurrent.verifier.finish_query_dot_loop.body ops bytes
   (SAG_DotAdapter.mapSlice NHE_DotRead.finishQ weights) t.1 t.2)
  sm rm (fun t=>weights.val.length-t.2.val) (step bytes weights size) (decreases bytes weights) s

#print axioms decreases
#print axioms cohort
end NHE_DotLoop
