import NGV_ChunkPredicate
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_ChunkCheck
open AspisR1PrefixAggregateParser
noncomputable def invoke (row : U8) (i : Usize) (bs : Slice U8) :
 Result (core.result.Result Unit r1_wire.Error) := do
 let wide ← field.wide_exact.WideExact.from_le_bytes bs
 match wide with
 | none => ok (.Err (.NonCanonical row i))
 | some w => do
   let high ← field.wide_exact.WideExact.impl.c1 w
   let bad ← core.cmp.PartialEq.ne.trait_default field.QM31.Insts.CoreCmpPartialEqQM31 high field.QM31.ZERO
   if bad then ok (.Err (.NonCanonical row i)) else ok (.Ok ())
theorem result (row : U8) (i : Usize) (bs : Slice U8) (size : bs.val.length=32) :
 invoke row i bs = ok (if NFU_Retarget.LPl_Kit_Bytes.validChunk 8 true bs.val
   then .Ok () else .Err (.NonCanonical row i)) := by
 unfold invoke
 rw [NGV_ChunkWords.parse bs size]
 change NGO_ValidatorCallback.invoke row i (NGV_ChunkWords.words bs size)=_
 rw [NGO_ValidatorCallback.result]
 have equivalence := NGV_ChunkPredicate.valid bs size
 by_cases h : NFU_Retarget.LPl_Kit_Bytes.validChunk 8 true bs.val=true
 · simp only [if_pos (equivalence.mp h),h,if_true]
 · simp only [if_neg (fun p => h (equivalence.mpr p)),if_neg h]
#print axioms result
end NGV_ChunkCheck
