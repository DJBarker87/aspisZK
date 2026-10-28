import PV_L2C_ChunkShape
import PV_L2C_AbsorbRange
import PV_L2C_HashRange
set_option autoImplicit false
namespace PV_L2C_HashTotal
open Aeneas Aeneas.Std Result R1Z R0Z.WriterRefine
open BuilderForestStdPort BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
local instance : Fact (Nat.Prime 2147483647) := ⟨R0Z.m31_prime⟩
abbrev callback := PV_L2C_HashLoopRange.callback

/-- The planner's bounded hash calls need no source-success premise. The
entire actual absorb/permutation/chunk-loop Result is successful. -/
theorem loop (i : PV_L2C_ChunkStep.Iter) (hs : i.iter.size = 8)
    (hb : i.count.val+i.iter.remaining.val.length ≤ 20)
    (hx : ∀ x ∈ i.iter.remaining.val, x.val < 2147483647)
    (s : State) (hc : Canonical s) :
    ∃ out, poseidon2.hash_fields_with_trace_loop0 callback i () s = ok out ∧ Canonical out := by
  generalize he : i.iter.remaining.val.length = n
  induction n using Nat.strong_induction_on generalizing i s with
  | h n ih =>
    by_cases empty : i.iter.remaining.val = []
    · refine ⟨s,?_,hc⟩
      rw [poseidon2.hash_fields_with_trace_loop0.eq_1,PV_L2C_ChunkShape.done i empty]
      rfl
    · have count : i.count.val < 24 := by omega
      have next := PV_L2C_ChunkShape.step i hs empty count
      obtain ⟨absorbed,ha,hca⟩ := PV_L2C_AbsorbRange.entry
        (PV_L2C_ChunkShape.head i.iter.remaining) (PV_L2C_ChunkShape.head_length _)
        (PV_L2C_ChunkShape.head_canonical _ hx) s hc
      obtain ⟨expected,hperm,hcan,_⟩ :=
        PV_RunJoin_HashCallback17.permutation (K := ZMod 2147483647) i.count absorbed
      obtain ⟨out,ho,hout⟩ := ih
        (PV_L2C_ChunkShape.advance i).iter.remaining.val.length
        (by have hlt := PV_L2C_ChunkShape.tail_shorter i.iter.remaining empty; exact he ▸ hlt)
        (PV_L2C_ChunkShape.advance i) rfl (PV_L2C_ChunkShape.advance_bound i hb empty)
        (PV_L2C_ChunkShape.tail_canonical _ hx) expected hcan rfl
      refine ⟨out,?_,hout⟩
      rw [poseidon2.hash_fields_with_trace_loop0.eq_1,next]
      simp only [bind_tc_ok,core.slice.Slice.iter,
        core.iter.traits.iterator.Iterator.enumerate.trait_default,
        core.iter.traits.iterator.Iterator.enumerate.default]
      rw [ha]
      simp only [bind_tc_ok]
      rw [hperm]
      exact ho
#print axioms loop

theorem source (domain : U32) (input : Slice U32) (hd : domain.val < 2147483647)
    (hl : input.val.length ≤ 20) (hne : input.val ≠ [])
    (hx : ∀ x ∈ input.val, x.val < 2147483647) :
    ∃ d, poseidon2.hash_fields domain input = ok d ∧ Canon8 d := by
  obtain ⟨s,hs,hcan⟩ := loop ⟨⟨input,8⟩,0#usize⟩ rfl (by simpa using hl) hx
    (PV_L2C_HashRange.initial domain input)
    (PV_L2C_HashRange.initial_canonical domain input hd (by omega))
  refine ⟨digest8 s,?_,?_⟩
  · rw [PV_L2C_HashRange.shape domain input hne,hs]
    rfl
  · intro j hj
    rw [digest8_get s j hj]
    exact hcan ⟨j,by omega⟩
#print axioms source
end PV_L2C_HashTotal
