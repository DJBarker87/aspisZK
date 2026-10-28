import NCJ_ConstructorSuccessor
set_option autoImplicit false
namespace NCJ_ConstructorPoints
open Aeneas Aeneas.Std Result NCJ_ConstructorQM NCJ_ConstructorArrays

theorem source (z : Array Q 10#usize) (hz : Holds Canon z) :
    ∃ out,FIn_WeightsExtract.state_only_prefix.state_only_statement_points z=ok out ∧
      Holds (Holds Canon) out := by
  have reverse : core.iter.traits.iterator.Iterator.rev.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
      {start:=0#usize,«end»:=10#usize}=ok (NCJ_Reverse.cursor 10#usize) := by rfl
  have size : Slice.len z.to_slice=10#usize := by apply UScalar.eq_of_val_eq;exact z.property
  obtain ⟨successor,run,canonical⟩ := NCJ_ConstructorSuccessor.source z z
    FIn_WeightsExtract.field.QM31.ONE hz hz one 10#usize (by decide)
  let q7 := NCJ_GuardExact.pick z 7 (by decide)
  have r7 := NCJ_GuardExact.index z 7#usize (by decide)
  change Array.index_usize z 7#usize=ok q7 at r7
  have c7 := canonical_pick Canon z 7 (by decide) hz
  obtain ⟨v7,h7,cv7⟩ := sub FIn_WeightsExtract.field.QM31.ONE q7 one c7
  let middle := put z 7 v7
  have u7 := update z 7#usize v7 (by decide)
  change Array.update z 7#usize v7=ok middle at u7
  have cp := canonical_put Canon z 7 v7 hz cv7
  let q6 := NCJ_GuardExact.pick middle 6 (by decide)
  have r6 := NCJ_GuardExact.index middle 6#usize (by decide)
  change Array.index_usize middle 6#usize=ok q6 at r6
  have c6 := canonical_pick Canon middle 6 (by decide) cp
  obtain ⟨v6,h6,cv6⟩ := sub FIn_WeightsExtract.field.QM31.ONE q6 one c6
  let absorption := put middle 6 v6
  have u6 := update middle 6#usize v6 (by decide)
  change Array.update middle 6#usize v6=ok absorption at u6
  have ca := canonical_put Canon middle 6 v6 cp cv6
  refine ⟨Array.make 3#usize [z,successor,absorption],?_,?_⟩
  · simp only [FIn_WeightsExtract.state_only_prefix.state_only_statement_points,
      lift,size,reverse,run,r7,h7,u7,r6,h6,u6,bind_tc_ok]
  · intro row hrow
    simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hrow
    rcases hrow with rfl|rfl|rfl
    · exact hz
    · exact canonical
    · exact ca

theorem wrapper (z : Array Q 10#usize) (hz : Holds Canon z) :
    ∃ out,FIn_WeightsExtract.state_only_prefix.r0.statement_points z=ok out ∧
      Holds (Holds Canon) out := source z hz

#print axioms source
#print axioms wrapper
end NCJ_ConstructorPoints
