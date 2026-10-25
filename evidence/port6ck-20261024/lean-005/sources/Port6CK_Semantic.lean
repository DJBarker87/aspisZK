import Port5Q2_ReaderSemantic
import Port5Q2_ReaderScalar
import CheckpointBytes4ReaderFields
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_Semantic
open Aeneas Aeneas.Std Result AspisR1Stage2
abbrev Unwrap := (N : Usize) → core.result.Result (Array U8 N) core.array.TryFromSliceError → Result (Array U8 N)
def current (unwrap : Unwrap) := Port5Q2_ReaderScalar.readK
  (fun N => Port5Q2_ReaderRaw.raw N (unwrap N)) Port5Q2_ReaderScalar.decodeK

/-- One reached read; the continuation is compared only on that exact call. -/
theorem withK_current {T : Type} (unwrap : Unwrap)
    (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b)
    (r : verifier.Reader) (room : r.at.val+16≤r.bytes.val.length)
    (size : r.bytes.val.length≤4096)
    (left right : aspis_core.field.QM31 → verifier.Reader → Result (core.result.Result T verifier.Error))
    (next : ∀ x out, CheckpointBytes3Reader.readK r=ok (.Ok x,out) → left x out=right x out) :
    CheckpointBytes4Ops.withK (current unwrap) r left =
      CheckpointBytes4Ops.withK CheckpointBytes3Reader.readK r right := by
  unfold CheckpointBytes4Ops.withK
  rw [show current unwrap r=CheckpointBytes3Reader.readK r from
    Port5Q2_ReaderScalar.current_k unwrap unwrap_ok r room size]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair called
  rcases pair with ⟨value,out⟩
  cases value with
  | Err e => rfl
  | Ok x => exact next x out called

/-- Ten CURRENT reads on the same backing, preserving all decoder failures. -/
theorem reference (unwrap : Unwrap) (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b)
    (bytes : Slice U8) (start : Usize)
    (room : start.val+160≤bytes.val.length) (size : bytes.val.length≤4096) :
    Port5Q2_ReaderSemantic.semantic (current unwrap) bytes start =
      CheckpointBytes4Ops.readSemanticAlpha bytes start := by
  rw [Port5Q2_ReaderSemantic.normalization]
  unfold CheckpointBytes4Ops.readSemanticAlpha CheckpointBytes4Ops.semanticUsing
  let r0 : verifier.Reader := ⟨bytes,start⟩
  have room0 : r0.at.val+160≤r0.bytes.val.length := room
  have size0 : r0.bytes.val.length≤4096 := size
  change CheckpointBytes4Ops.withK (current unwrap) r0 _ = CheckpointBytes4Ops.withK CheckpointBytes3Reader.readK r0 _
  apply withK_current unwrap unwrap_ok r0 (by omega) size0
  intro x0 r1 called0
  obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success
    r0 r1 x0 (by omega) called0
  have room1 : r1.at.val+144≤r1.bytes.val.length := by rw [cursor,backing]; omega
  have size1 : r1.bytes.val.length≤4096 := by rw [backing]; exact size0
  apply withK_current unwrap unwrap_ok r1 (by omega) size1
  intro x1 r2 called1
  obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success
    r1 r2 x1 (by omega) called1
  have room2 : r2.at.val+128≤r2.bytes.val.length := by rw [cursor,backing]; omega
  have size2 : r2.bytes.val.length≤4096 := by rw [backing]; exact size1
  apply withK_current unwrap unwrap_ok r2 (by omega) size2
  intro x2 r3 called2
  obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success
    r2 r3 x2 (by omega) called2
  have room3 : r3.at.val+112≤r3.bytes.val.length := by rw [cursor,backing]; omega
  have size3 : r3.bytes.val.length≤4096 := by rw [backing]; exact size2
  apply withK_current unwrap unwrap_ok r3 (by omega) size3
  intro x3 r4 called3
  obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success
    r3 r4 x3 (by omega) called3
  have room4 : r4.at.val+96≤r4.bytes.val.length := by rw [cursor,backing]; omega
  have size4 : r4.bytes.val.length≤4096 := by rw [backing]; exact size3
  apply withK_current unwrap unwrap_ok r4 (by omega) size4
  intro x4 r5 called4
  obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success
    r4 r5 x4 (by omega) called4
  have room5 : r5.at.val+80≤r5.bytes.val.length := by rw [cursor,backing]; omega
  have size5 : r5.bytes.val.length≤4096 := by rw [backing]; exact size4
  apply withK_current unwrap unwrap_ok r5 (by omega) size5
  intro x5 r6 called5
  obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success
    r5 r6 x5 (by omega) called5
  have room6 : r6.at.val+64≤r6.bytes.val.length := by rw [cursor,backing]; omega
  have size6 : r6.bytes.val.length≤4096 := by rw [backing]; exact size5
  apply withK_current unwrap unwrap_ok r6 (by omega) size6
  intro x6 r7 called6
  obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success
    r6 r7 x6 (by omega) called6
  have room7 : r7.at.val+48≤r7.bytes.val.length := by rw [cursor,backing]; omega
  have size7 : r7.bytes.val.length≤4096 := by rw [backing]; exact size6
  apply withK_current unwrap unwrap_ok r7 (by omega) size7
  intro x7 r8 called7
  obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success
    r7 r8 x7 (by omega) called7
  have room8 : r8.at.val+32≤r8.bytes.val.length := by rw [cursor,backing]; omega
  have size8 : r8.bytes.val.length≤4096 := by rw [backing]; exact size7
  apply withK_current unwrap unwrap_ok r8 (by omega) size8
  intro x8 r9 called8
  obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success
    r8 r9 x8 (by omega) called8
  have room9 : r9.at.val+16≤r9.bytes.val.length := by rw [cursor,backing]; omega
  have size9 : r9.bytes.val.length≤4096 := by rw [backing]; exact size8
  apply withK_current unwrap unwrap_ok r9 (by omega) size9
  intro x9 r10 called9
  rfl
/-- Concrete op18 semantic section: 408 through568, on the S2 body. -/
theorem at408 (unwrap : Unwrap) (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b)
    (bytes : Slice U8) (length : bytes.val.length=1768) :
    Port5Q2_ReaderSemantic.semantic (current unwrap) bytes 408#usize =
      CheckpointBytes4Ops.readSemanticAlpha bytes 408#usize :=
  reference unwrap unwrap_ok bytes 408#usize (by rw [length]; decide) (by omega)

#print axioms withK_current
#print axioms reference
#print axioms at408
end AspisR1.Port6CK_Semantic
end
