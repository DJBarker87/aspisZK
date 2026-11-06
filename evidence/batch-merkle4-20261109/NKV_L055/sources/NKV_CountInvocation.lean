import NKV_ConcreteDomains
import Port4B_SliceReads
set_option autoImplicit false
noncomputable section
namespace NKV_CountInvocation
open Aeneas Aeneas.Std Result AspisR1 MultiproofConeRef
open OraclePortFrozenOrder
attribute [local instance] Classical.propDecidable

def front (s : reference.Scratch) : Slice U32 :=
 ⟨s.idx.val.take s.n.val,by have len:=s.idx.property;simp only [List.length_take];scalar_tac⟩

theorem read (s : reference.Scratch) (bound : s.n.val≤16) :
 core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32))
   s.idx {«end»:=s.n}=ok (front s) := by
 simp only [Array.index_SliceIndexRangeToUsizeSlice,core.slice.index.SliceIndexRangeToUsizeSlice.index]
 split
 · rfl
 · next bad => exact (bad (by simpa using bound)).elim

theorem keys (s : reference.Scratch) (bound : s.n.val≤16) :
 (front s).val.map (fun x : U32 => x.val)=NJV_UnitDomain.keys s :=
 Port4B_SliceReads.live_indices s (front s) (read s bound)

/-- Exact all-Option child relation at the SAME physical index prefix. -/
theorem source (s : reference.Scratch) (bound : s.n.val≤16) :
 ∃ out : Option Usize,NKV_ConcreteChildren.count .Two (front s)=ok out ∧
 out.map (fun x : Usize => x.val)=
 (if wellFormed (NJV_UnitDomain.keys s) then some (nodeCount 18 (NJV_UnitDomain.keys s)) else none) := by
 obtain ⟨out,run,value⟩:=NKV_ConcreteDomains.count (front s)
 rw [keys s bound] at value
 exact ⟨out,run,value⟩

theorem present (s : reference.Scratch) (bound : s.n.val≤16)
 (well : wellFormed (NJV_UnitDomain.keys s)) :
 ∃ count,NKV_ConcreteChildren.count .Two (front s)=ok (some count) ∧
 count.val=nodeCount 18 (NJV_UnitDomain.keys s) := by
 obtain ⟨out,run,value⟩:=source s bound
 rw [if_pos well] at value
 cases out with
 | none => cases value
 | some count => exact ⟨count,run,Option.some.inj value⟩

theorem missing (s : reference.Scratch) (bound : s.n.val≤16)
 (bad : ¬wellFormed (NJV_UnitDomain.keys s)) :
 NKV_ConcreteChildren.count .Two (front s)=ok none := by
 obtain ⟨out,run,value⟩:=source s bound
 rw [if_neg bad] at value
 cases out with
 | none => exact run
 | some count => cases value

set_option pp.proofs false
#print source
#print present
#print missing
#print axioms read
#print axioms keys
#print axioms source
#print axioms present
#print axioms missing
end NKV_CountInvocation
end
