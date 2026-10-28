import NDF_ChunkCodec
set_option autoImplicit false
namespace NDF_CodecTotal
open Aeneas Aeneas.Std Result
open AspisR1RecordParser.field
open AspisR1.ExtractedRecordByteCanonicality AspisR1.ExtractedRecordLimbCanonicality
open AspisR1.ExtractedRecordHighZero
attribute [local instance] Classical.propDecidable

theorem decode (arr : Array U8 32#usize) :
    ∃ value, wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok value := by
  rw [fixed_reads,wordArray8,from_limbs_make]
  exact ⟨_,rfl⟩

theorem compare_total (q : QM31) :
    ∃ value, core.cmp.PartialEq.ne.trait_default QM31.Insts.CoreCmpPartialEqQM31 q QM31.ZERO=ok value := by
  rcases q with ⟨⟨a,b⟩,⟨c,d⟩⟩
  simp only [core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    QM31.Insts.CoreCmpPartialEqQM31,QM31.Insts.CoreCmpPartialEqQM31.eq,
    CM31.Insts.CoreCmpPartialEqCM31.eq,M31.Insts.CoreCmpPartialEqM31.eq,QM31.ZERO,bind_tc_ok]
  split_ifs <;> simp_all only [bind_tc_ok] <;> exact ⟨_,rfl⟩

theorem compare (q : QM31) :
    core.cmp.PartialEq.ne.trait_default QM31.Insts.CoreCmpPartialEqQM31 q QM31.ZERO = ok (decide (q≠QM31.ZERO)) := by
  obtain ⟨value,call⟩ := compare_total q
  have law := qm31_ne_false_iff q QM31.ZERO
  by_cases zero : q=QM31.ZERO
  · simpa only [zero,ne_eq,not_true_eq_false,decide_false] using law.mpr zero
  · have nonfalse : value≠false := by
      intro bad
      rw [bad] at call
      exact zero (law.mp call)
    have yes : value=true := by cases value <;> simp_all
    simp only [call,yes,zero,ne_eq,not_false_eq_true,decide_true]

#print axioms decode
#print axioms compare_total
#print axioms compare
end NDF_CodecTotal
