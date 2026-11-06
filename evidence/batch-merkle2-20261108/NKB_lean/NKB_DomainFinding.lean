import NKB_StrictLeaves
import NJV_UnitDomain

set_option autoImplicit false
noncomputable section
namespace NKB_DomainFinding
open Aeneas Aeneas.Std Result MultiproofConeRef AspisR1
open MultiproofConeLiveFold

/-- TX2 tree0/tree1: queries[10..22] are twelve distinct canonical indices.
Digest replies are arbitrary; no consistency/success hypothesis is needed. -/
def leaves (digest : Fin 12 → Array U8 32#usize) : List Leaf :=
 List.ofFn (fun j : Fin 12 =>
   ((UScalar.ofNat (10+j.val) (by have h:=j.isLt;scalar_tac) : U32),digest j))

theorem indices (digest : Fin 12 → Array U8 32#usize) :
 (leaves digest).map (fun x => x.1.val)=NKB_StrictCount.tx2Indices := by
 apply List.ext_getElem
 · simp only [leaves,NKB_StrictCount.tx2Indices,List.length_map,List.length_ofFn,List.length_range]
 · intro j hj hj'
   simp only [leaves,NKB_StrictCount.tx2Indices,List.getElem_map,List.getElem_ofFn,List.getElem_range]
   rfl

/-- An explicit count/caller-domain counterexample indexed by the SAME full
scratch and verifier entry arrays. No whole-batch success or hash law is assumed.
This does not refute NJV's broader entry refinement; it refutes imposing its
separately retained ten-leaf unit clause on every valid TX2 call. -/
theorem unit_counterexample (digest : Fin 12 → Array U8 32#usize)
    (before : reference.Scratch) (empty : before.n.val=0) (physical slot : Slice U8) :
 ∃ after, NKB_LeafChain.Chain (leaves digest) before (some after) ∧
   after.n.val=12 ∧
   ¬NJV_UnitDomain.Domain physical slot (NJV_EntryABI.initial after.idx after.val after.n) := by
 obtain ⟨after,chain,count,notTen⟩ := NKB_StrictLeaves.twelve (leaves digest) before empty (indices digest)
 refine ⟨after,chain,count,?_⟩
 intro domain
 exact notTen domain.batch

set_option pp.proofs false
#print unit_counterexample
#print axioms indices
#print axioms unit_counterexample
end NKB_DomainFinding
end
