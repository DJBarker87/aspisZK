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

/-- Ten CURRENT reads on the same backing, preserving all decoder failures.
The only guards are section room and the concrete checked/wrapping range. -/
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
  unfold CheckpointBytes4Ops.withK
  rw [show current unwrap r0=CheckpointBytes3Reader.readK r0 from
    Port5Q2_ReaderScalar.current_k unwrap unwrap_ok r0 (by omega) size0]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair called0
  rcases pair with ⟨value,r1⟩
  cases value with
  | Err e => rfl
  | Ok x0 =>
    obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success
      r0 r1 x0 (by omega) called0
    have room1 : r1.at.val+144≤r1.bytes.val.length := by rw [cursor,backing]; omega
    have size1 : r1.bytes.val.length≤4096 := by rw [backing]; exact size0
    dsimp only
    unfold CheckpointBytes4Ops.withK
    rw [show current unwrap r1=CheckpointBytes3Reader.readK r1 from
      Port5Q2_ReaderScalar.current_k unwrap unwrap_ok r1 (by omega) size1]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro pair called1
    rcases pair with ⟨value,r2⟩
    cases value with
    | Err e => rfl
    | Ok x1 =>
      obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success
        r1 r2 x1 (by omega) called1
      have room2 : r2.at.val+128≤r2.bytes.val.length := by rw [cursor,backing]; omega
      have size2 : r2.bytes.val.length≤4096 := by rw [backing]; exact size1
      dsimp only
      unfold CheckpointBytes4Ops.withK
      rw [show current unwrap r2=CheckpointBytes3Reader.readK r2 from
        Port5Q2_ReaderScalar.current_k unwrap unwrap_ok r2 (by omega) size2]
      apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro pair called2
      rcases pair with ⟨value,r3⟩
      cases value with
      | Err e => rfl
      | Ok x2 =>
        obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success
          r2 r3 x2 (by omega) called2
        have room3 : r3.at.val+112≤r3.bytes.val.length := by rw [cursor,backing]; omega
        have size3 : r3.bytes.val.length≤4096 := by rw [backing]; exact size2
        dsimp only
        unfold CheckpointBytes4Ops.withK
        rw [show current unwrap r3=CheckpointBytes3Reader.readK r3 from
          Port5Q2_ReaderScalar.current_k unwrap unwrap_ok r3 (by omega) size3]
        apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro pair called3
        rcases pair with ⟨value,r4⟩
        cases value with
        | Err e => rfl
        | Ok x3 =>
          obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success
            r3 r4 x3 (by omega) called3
          have room4 : r4.at.val+96≤r4.bytes.val.length := by rw [cursor,backing]; omega
          have size4 : r4.bytes.val.length≤4096 := by rw [backing]; exact size3
          dsimp only
          unfold CheckpointBytes4Ops.withK
          rw [show current unwrap r4=CheckpointBytes3Reader.readK r4 from
            Port5Q2_ReaderScalar.current_k unwrap unwrap_ok r4 (by omega) size4]
          apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
          intro pair called4
          rcases pair with ⟨value,r5⟩
          cases value with
          | Err e => rfl
          | Ok x4 =>
            obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success
              r4 r5 x4 (by omega) called4
            have room5 : r5.at.val+80≤r5.bytes.val.length := by rw [cursor,backing]; omega
            have size5 : r5.bytes.val.length≤4096 := by rw [backing]; exact size4
            dsimp only
            unfold CheckpointBytes4Ops.withK
            rw [show current unwrap r5=CheckpointBytes3Reader.readK r5 from
              Port5Q2_ReaderScalar.current_k unwrap unwrap_ok r5 (by omega) size5]
            apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
            intro pair called5
            rcases pair with ⟨value,r6⟩
            cases value with
            | Err e => rfl
            | Ok x5 =>
              obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success
                r5 r6 x5 (by omega) called5
              have room6 : r6.at.val+64≤r6.bytes.val.length := by rw [cursor,backing]; omega
              have size6 : r6.bytes.val.length≤4096 := by rw [backing]; exact size5
              dsimp only
              unfold CheckpointBytes4Ops.withK
              rw [show current unwrap r6=CheckpointBytes3Reader.readK r6 from
                Port5Q2_ReaderScalar.current_k unwrap unwrap_ok r6 (by omega) size6]
              apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
              intro pair called6
              rcases pair with ⟨value,r7⟩
              cases value with
              | Err e => rfl
              | Ok x6 =>
                obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success
                  r6 r7 x6 (by omega) called6
                have room7 : r7.at.val+48≤r7.bytes.val.length := by rw [cursor,backing]; omega
                have size7 : r7.bytes.val.length≤4096 := by rw [backing]; exact size6
                dsimp only
                unfold CheckpointBytes4Ops.withK
                rw [show current unwrap r7=CheckpointBytes3Reader.readK r7 from
                  Port5Q2_ReaderScalar.current_k unwrap unwrap_ok r7 (by omega) size7]
                apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
                intro pair called7
                rcases pair with ⟨value,r8⟩
                cases value with
                | Err e => rfl
                | Ok x7 =>
                  obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success
                    r7 r8 x7 (by omega) called7
                  have room8 : r8.at.val+32≤r8.bytes.val.length := by rw [cursor,backing]; omega
                  have size8 : r8.bytes.val.length≤4096 := by rw [backing]; exact size7
                  dsimp only
                  unfold CheckpointBytes4Ops.withK
                  rw [show current unwrap r8=CheckpointBytes3Reader.readK r8 from
                    Port5Q2_ReaderScalar.current_k unwrap unwrap_ok r8 (by omega) size8]
                  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
                  intro pair called8
                  rcases pair with ⟨value,r9⟩
                  cases value with
                  | Err e => rfl
                  | Ok x8 =>
                    obtain ⟨decoded,decode,valueEq,cursor,backing⟩ := CheckpointBytes4ReaderFields.k_success
                      r8 r9 x8 (by omega) called8
                    have room9 : r9.at.val+16≤r9.bytes.val.length := by rw [cursor,backing]; omega
                    have size9 : r9.bytes.val.length≤4096 := by rw [backing]; exact size8
                    dsimp only
                    unfold CheckpointBytes4Ops.withK
                    rw [show current unwrap r9=CheckpointBytes3Reader.readK r9 from
                      Port5Q2_ReaderScalar.current_k unwrap unwrap_ok r9 (by omega) size9]
                    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
                    intro pair called9
                    rcases pair with ⟨value,r10⟩
                    cases value with
                    | Err e => rfl
                    | Ok x9 =>
                      rfl

/-- Concrete op18 semantic section: 408 through568, on the S2 body. -/
theorem at408 (unwrap : Unwrap) (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b)
    (bytes : Slice U8) (length : bytes.val.length=1768) :
    Port5Q2_ReaderSemantic.semantic (current unwrap) bytes 408#usize =
      CheckpointBytes4Ops.readSemanticAlpha bytes 408#usize :=
  reference unwrap unwrap_ok bytes 408#usize (by rw [length]; decide) (by omega)

#print axioms reference
#print axioms at408
end AspisR1.Port6CK_Semantic
end
