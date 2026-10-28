import R1Z.PV_RunJoin_HashCallback17
import R1Z.PV_RunJoin_HeadControl29
set_option autoImplicit false
namespace PV_L2C_ChunkStep
open Aeneas Aeneas.Std Result R1Z R1Z.BuilderForestStdPort

abbrev Iter := core.iter.adapters.enumerate.Enumerate (core.slice.iter.Chunks U32)
abbrev next := core.iter.adapters.enumerate.IteratorEnumerate.next
  (core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice U32)

/-- Every yielded native chunk strictly reduces the remaining source slice.
This is iterator geometry, independent of any field computation. -/
theorem returned (i j : Iter) (p : Usize × Slice U32) (hs : 0 < i.iter.size)
    (h : next i = ok (some p,j)) :
    j.iter.size = i.iter.size ∧
    j.iter.remaining.val.length < i.iter.remaining.val.length := by
  unfold next core.iter.adapters.enumerate.IteratorEnumerate.next at h
  change (do
    let (o,it) ← BuilderForestStd.chunksNext i.iter
    match o with
    | none => ok (none,{i with iter := it})
    | some x => do
      let n ← i.count + 1#usize
      ok (some (i.count,x),⟨it,n⟩)) = ok (some p,j) at h
  unfold BuilderForestStd.chunksNext at h
  split at h
  · simp only [bind_tc_ok] at h
    cases h
  · rename_i hn
    simp only [bind_tc_ok] at h
    pv_peel h with n hnum
    cases h
    refine ⟨rfl,?_⟩
    simp only [List.length_drop]
    have hne : i.iter.remaining.val ≠ [] := by
      intro he
      simp only [he,List.isEmpty_nil] at hn
      contradiction
    have hl : 0 < i.iter.remaining.val.length := List.length_pos_iff.mpr hne
    omega
#print axioms returned
end PV_L2C_ChunkStep
