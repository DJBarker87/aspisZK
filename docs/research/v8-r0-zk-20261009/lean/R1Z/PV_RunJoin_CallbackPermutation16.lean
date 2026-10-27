import R1Z.PV_RunJoin_CallbackRounds16
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CallbackPermutation16
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestStdPort BuilderForestAdmissionPort PV_Src_PortSboxStep
variable {K F : Type} [Field K] [CharP K 2147483647]

def run (callback : core.ops.function.FnMut F poseidon2.Poseidon2RoundTransition Unit)
    (s : State) (trace : F) : Result (State × F) := do
  let first ← PV_Src_ExternalReference.run s
  let (a,t,r,i) ← poseidon2.permute_optimized_with_trace_loop0
    (sourceExternalLinear := PV_Src_ExternalReference.dictionary) callback
    ⟨⟨Array.to_slice poseidon2.EXTERNAL_INITIAL,0⟩,0#usize⟩ first trace 0#u8 s
  let (b,t1,r1,i1) ← poseidon2.permute_optimized_with_trace_loop1
    callback ⟨poseidon2.INTERNAL.val,0#usize⟩ a t r i
  poseidon2.permute_optimized_with_trace_loop2
    (sourceExternalLinear := PV_Src_ExternalReference.dictionary) callback
    ⟨⟨Array.to_slice poseidon2.EXTERNAL_FINAL,0⟩,0#usize⟩ b t1 r1 i1

theorem shape (callback : core.ops.function.FnMut F poseidon2.Poseidon2RoundTransition Unit)
    (s : State) (trace : F) :
    poseidon2.permute_optimized_with_trace_threaded
      (sourceExternalLinear := PV_Src_ExternalReference.dictionary) callback s trace = run callback s trace := by rfl

theorem source (callback : core.ops.function.FnMut F poseidon2.Poseidon2RoundTransition Unit)
    (trace : F) (hc : ∀ event, callback.call_mut trace event = ok ((),trace)) (s : State) :
    ∃ out : State,
      poseidon2.permute_optimized_with_trace_threaded
        (sourceExternalLinear := PV_Src_ExternalReference.dictionary) callback s trace = ok (out,trace) ∧
      Canonical out ∧ liftA (K := K) out = R0P.poseidonPermutation (liftA s) := by
  obtain ⟨first,hfirst,hmeaning⟩ := external_lift (K := K) s
  have hcan : Canonical first := fun j => external_canon s first hfirst j.val j.isLt
  obtain ⟨a,ha,hca,hta,hma⟩ := PV_RunJoin_CallbackRounds16.initial (K := K) callback trace hc first s 0#u8 hcan
  rcases a with ⟨sa,ta,ra,ia⟩
  dsimp only at hta
  subst ta
  obtain ⟨b,hb,hcb,htb,hmb⟩ := PV_RunJoin_CallbackRounds16.internal (K := K) callback trace hc sa ia ra hca
  rcases b with ⟨sb,tb,rb,ib⟩
  dsimp only at htb
  subst tb
  obtain ⟨out,ho,hco,hmo⟩ := PV_RunJoin_CallbackRounds16.final_rounds (K := K) callback trace hc sb ib rb hcb
  refine ⟨out,?_,hco,?_⟩
  · rw [shape,run,PV_Src_ExternalCopy.source,hfirst]
    simp only [bind_tc_ok,ha]
    change (do
      let (b,t1,r1,i1) ← poseidon2.permute_optimized_with_trace_loop1
        callback ⟨poseidon2.INTERNAL.val,0#usize⟩ sa trace ra ia
      poseidon2.permute_optimized_with_trace_loop2
        (sourceExternalLinear := PV_Src_ExternalReference.dictionary) callback
        ⟨⟨Array.to_slice poseidon2.EXTERNAL_FINAL,0⟩,0#usize⟩ b t1 r1 i1) = ok (out,trace)
    rw [hb]
    change poseidon2.permute_optimized_with_trace_loop2
      (sourceExternalLinear := PV_Src_ExternalReference.dictionary) callback
      ⟨⟨Array.to_slice poseidon2.EXTERNAL_FINAL,0⟩,0#usize⟩ sb trace rb ib = ok (out,trace)
    exact ho
  · rw [hmo,hmb,hma,show liftA (K := K) first = _ from funext hmeaning]
    exact PV_Src_PortPermutation.model _
#print axioms shape
#print axioms source
end R1Z.PV_RunJoin_CallbackPermutation16
