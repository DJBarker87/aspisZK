import XRz_PushReach
import XRk_ResultTools
open Aeneas Aeneas.Std Result XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XSc_AccumulateCuts
/-- The actual successful accumulation fixes its basis, pending continuation,
power multiplication and checked counters. No independent execution is chosen. -/
theorem source (p : verifier.Prepared) (a out : verifier.Accumulator)
 (node : aspis_core.field.M31) (value : aspis_core.field.wide_exact.WideExact)
 (pending after : verifier.BatchedWeights)
 (run : verifier.accumulate_batched_with_node p a node value pending=ok (out,after)) :
 ∃ (one : aspis_core.field.M31) (basis : Array aspis_core.field.M31 256#usize)
 (rows : verifier.BatchedWeights),
 aspis_core.field.M31.ONE=ok one ∧
 verifier.accumulate_batched_with_node_loop1
  {start:=0#usize,«end»:=alloc.vec.Vec.len a.weights}
  a.weights a.power a.next pending (alloc.vec.Vec.len a.weights) basis=ok rows ∧
 (rows.terms+1#usize : Result Usize)=ok after.terms ∧
 aspis_core.field.QM31.mul a.power p.rho=ok out.power ∧
 (a.next+1#usize : Result Usize)=ok out.next ∧
 out.weights=a.weights ∧ after.raw=rows.raw := by
 unfold verifier.accumulate_batched_with_node at run
 obtain ⟨zero,_,run⟩ := bind_success _ _ _ run
 obtain ⟨one,hone,run⟩ := bind_success _ _ _ run
 obtain ⟨basis0,_,run⟩ := bind_success _ _ _ run
 obtain ⟨basis,hbasis,run⟩ := bind_success _ _ _ run
 obtain ⟨rows,hrows,run⟩ := bind_success _ _ _ run
 obtain ⟨terms,hterms,run⟩ := bind_success _ _ _ run
 obtain ⟨product,_,run⟩ := bind_success _ _ _ run
 obtain ⟨rhs,_,run⟩ := bind_success _ _ _ run
 obtain ⟨marked,_,run⟩ := bind_success _ _ _ run
 obtain ⟨power,hpower,run⟩ := bind_success _ _ _ run
 obtain ⟨next,hnext,run⟩ := bind_success _ _ _ run
 cases Result.ok.inj run
 exact ⟨one,basis,rows,hone,hrows,hterms,hpower,hnext,rfl,rfl⟩
#print axioms source
end XSc_AccumulateCuts
