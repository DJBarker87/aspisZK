import XSe_BasisOuter
open Aeneas Aeneas.Std Result XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XSe_AccumulateBasis
open XSe_BasisUpdate
/-- Actual basis provenance at this successful accumulation call. Canonicality
is DERIVED for every cell, rather than assumed at each emitted push. -/
theorem source (p : verifier.Prepared) (a out : verifier.Accumulator)
 (node : aspis_core.field.M31) (value : aspis_core.field.wide_exact.WideExact)
 (pending after : verifier.BatchedWeights)
 (run : verifier.accumulate_batched_with_node p a node value pending=ok (out,after)) :
 ∃ (basis : Basis) (rows : verifier.BatchedWeights), Canonical basis ∧
 verifier.accumulate_batched_with_node_loop1
  {start:=0#usize,«end»:=alloc.vec.Vec.len a.weights}
  a.weights a.power a.next pending (alloc.vec.Vec.len a.weights) basis=ok rows := by
 unfold verifier.accumulate_batched_with_node at run
 obtain ⟨zero,hzero,run⟩ := bind_success _ _ _ run
 obtain ⟨one,hone,run⟩ := bind_success _ _ _ run
 unfold aspis_core.field.M31.ZERO at hzero
 unfold aspis_core.field.M31.ONE at hone
 cases Result.ok.inj hzero
 cases Result.ok.inj hone
 obtain ⟨basis0,hbasis0,run⟩ := bind_success _ _ _ run
 obtain ⟨basis,hbasis,run⟩ := bind_success _ _ _ run
 obtain ⟨rows,hrows,run⟩ := bind_success _ _ _ run
 have repeated : Canonical (Array.repeat 256#usize (0#u32)) := by
  intro x hx
  simp only [Array.repeat,List.mem_replicate] at hx
  rcases hx with ⟨_,rfl⟩
  decide
 have fresh := XSe_BasisUpdate.source _ basis0 0#usize 1#u32 repeated (by decide) hbasis0
 exact ⟨basis,rows,XSe_BasisOuter.source 1#u32 node _ 1#usize basis0 basis fresh (by decide) hbasis,hrows⟩
#print axioms source
end XSe_AccumulateBasis
