import XSe_BasisOuter
import XSg_RowLoop
import XSc_AccumulateFrame
open Aeneas Aeneas.Std Result XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XSg_AccumulatePhase
open XSe_BasisUpdate
/-- Actual basis provenance at this successful accumulation call. Canonicality
is DERIVED for every cell, rather than assumed at each emitted push. -/
theorem source (p : verifier.Prepared) (a out : verifier.Accumulator)
 (node : aspis_core.field.M31) (value : aspis_core.field.wide_exact.WideExact)
 (pending after : verifier.BatchedWeights)
 (canon : XRp_PowersQAdd.CanonicalQ a.power)
 (small : a.weights.val.length≤256) (len : pending.raw.val.length=a.weights.val.length)
 (phase : ∀ row∈pending.raw.val,XSg_RowPhase.Bound pending.terms.val row)
 (run : verifier.accumulate_batched_with_node p a node value pending=ok (out,after)) :
 ∀ row∈after.raw.val,XSg_RowPhase.Bound after.terms.val row := by
 have frame := XSc_AccumulateFrame.source p a out node value pending after run
 have inc : after.terms.val=pending.terms.val+1 := by have h:=frame.2;scalar_tac
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
 have canonical := XSe_BasisOuter.source 1#u32 node _ 1#usize basis0 basis fresh (by decide) hbasis
 have advanced := XSg_RowLoop.source a.weights a.power a.next (alloc.vec.Vec.len a.weights) basis pending rows
  canon canonical (by simpa only [alloc.vec.Vec.len] using small) (by simpa only [alloc.vec.Vec.len] using len) phase hrows
 obtain ⟨terms,_,run⟩ := bind_success _ _ _ run
 obtain ⟨product,_,run⟩ := bind_success _ _ _ run
 obtain ⟨rhs,_,run⟩ := bind_success _ _ _ run
 obtain ⟨marked,_,run⟩ := bind_success _ _ _ run
 obtain ⟨power,_,run⟩ := bind_success _ _ _ run
 obtain ⟨next,_,run⟩ := bind_success _ _ _ run
 have same := Result.ok.inj run
 have raw : after.raw=rows.raw := by cases same;rfl
 rw [raw]
 intro row mem
 have h := advanced row mem
 simpa only [inc] using h
#print axioms source
end XSg_AccumulatePhase
