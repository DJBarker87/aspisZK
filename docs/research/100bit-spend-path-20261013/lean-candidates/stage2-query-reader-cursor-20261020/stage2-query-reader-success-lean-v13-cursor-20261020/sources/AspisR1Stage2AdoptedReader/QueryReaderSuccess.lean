import AspisR1Stage2AdoptedResume.Funs
import AspisR1Stage2AdoptedReader.RawCursorAdvanceNat
import AspisR1Stage2AdoptedReader.QueryCursorNatChain

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1Stage2AdoptedReader.QueryReaderSuccess

private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem bind_pair_success {A B C : Type} (m : Result (A × B))
    (k : A → B → Result C) (v : C)
    (h : (do let (a, b) ← m; k a b) = ok v) :
    ∃ a b, m = ok (a, b) ∧ k a b = ok v := by
  cases m with
  | ok pair => rcases pair with ⟨a, b⟩; exact ⟨a, b, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

abbrev Reader := _root_.AspisR1Stage2AdoptedResume.verifier.Reader
abbrev QueryArray := Array Std.U32 22#usize
abbrev Raw4 := Array Std.U8 4#usize

/-- Successful candidate execution exposes every ordered raw read and decode,
    the exact array passed to the opaque validation boundary, and the final cursor. -/
theorem successful_query_read_exposes_validation_call
    (validate_queries : (Array Std.U32 22#usize) → Result (core.result.Result (Array Std.U32 22#usize) _root_.AspisR1Stage2AdoptedResume.verifier.Error))
    (bytes : Slice Std.U8) (cursor0 : Usize) (queries : QueryArray) (finalAt : Usize)
    (h : _root_.AspisR1Stage2AdoptedResume.verifier.resume_read_queries validate_queries bytes cursor0 =
      ok (core.result.Result.Ok (queries, finalAt))) :
    ∃ r1 b0 q0 r2 b1 q1 r3 b2 q2 r4 b3 q3 r5 b4 q4 r6 b5 q5 r7 b6 q6 r8 b7 q7 r9 b8 q8 r10 b9 q9 r11 b10 q10 r12 b11 q11 r13 b12 q12 r14 b13 q13 r15 b14 q14 r16 b15 q15 r17 b16 q16 r18 b17 q17 r19 b18 q18 r20 b19 q19 r21 b20 q20 r22 b21 q21,
      _root_.AspisR1Stage2AdoptedResume.verifier.Reader.raw 4#usize { bytes, «at» := cursor0 } = ok (b0, r1) ∧
      lift (core.num.U32.from_le_bytes b0) = ok q0 ∧
      _root_.AspisR1Stage2AdoptedResume.verifier.Reader.raw 4#usize r1 = ok (b1, r2) ∧
      lift (core.num.U32.from_le_bytes b1) = ok q1 ∧
      _root_.AspisR1Stage2AdoptedResume.verifier.Reader.raw 4#usize r2 = ok (b2, r3) ∧
      lift (core.num.U32.from_le_bytes b2) = ok q2 ∧
      _root_.AspisR1Stage2AdoptedResume.verifier.Reader.raw 4#usize r3 = ok (b3, r4) ∧
      lift (core.num.U32.from_le_bytes b3) = ok q3 ∧
      _root_.AspisR1Stage2AdoptedResume.verifier.Reader.raw 4#usize r4 = ok (b4, r5) ∧
      lift (core.num.U32.from_le_bytes b4) = ok q4 ∧
      _root_.AspisR1Stage2AdoptedResume.verifier.Reader.raw 4#usize r5 = ok (b5, r6) ∧
      lift (core.num.U32.from_le_bytes b5) = ok q5 ∧
      _root_.AspisR1Stage2AdoptedResume.verifier.Reader.raw 4#usize r6 = ok (b6, r7) ∧
      lift (core.num.U32.from_le_bytes b6) = ok q6 ∧
      _root_.AspisR1Stage2AdoptedResume.verifier.Reader.raw 4#usize r7 = ok (b7, r8) ∧
      lift (core.num.U32.from_le_bytes b7) = ok q7 ∧
      _root_.AspisR1Stage2AdoptedResume.verifier.Reader.raw 4#usize r8 = ok (b8, r9) ∧
      lift (core.num.U32.from_le_bytes b8) = ok q8 ∧
      _root_.AspisR1Stage2AdoptedResume.verifier.Reader.raw 4#usize r9 = ok (b9, r10) ∧
      lift (core.num.U32.from_le_bytes b9) = ok q9 ∧
      _root_.AspisR1Stage2AdoptedResume.verifier.Reader.raw 4#usize r10 = ok (b10, r11) ∧
      lift (core.num.U32.from_le_bytes b10) = ok q10 ∧
      _root_.AspisR1Stage2AdoptedResume.verifier.Reader.raw 4#usize r11 = ok (b11, r12) ∧
      lift (core.num.U32.from_le_bytes b11) = ok q11 ∧
      _root_.AspisR1Stage2AdoptedResume.verifier.Reader.raw 4#usize r12 = ok (b12, r13) ∧
      lift (core.num.U32.from_le_bytes b12) = ok q12 ∧
      _root_.AspisR1Stage2AdoptedResume.verifier.Reader.raw 4#usize r13 = ok (b13, r14) ∧
      lift (core.num.U32.from_le_bytes b13) = ok q13 ∧
      _root_.AspisR1Stage2AdoptedResume.verifier.Reader.raw 4#usize r14 = ok (b14, r15) ∧
      lift (core.num.U32.from_le_bytes b14) = ok q14 ∧
      _root_.AspisR1Stage2AdoptedResume.verifier.Reader.raw 4#usize r15 = ok (b15, r16) ∧
      lift (core.num.U32.from_le_bytes b15) = ok q15 ∧
      _root_.AspisR1Stage2AdoptedResume.verifier.Reader.raw 4#usize r16 = ok (b16, r17) ∧
      lift (core.num.U32.from_le_bytes b16) = ok q16 ∧
      _root_.AspisR1Stage2AdoptedResume.verifier.Reader.raw 4#usize r17 = ok (b17, r18) ∧
      lift (core.num.U32.from_le_bytes b17) = ok q17 ∧
      _root_.AspisR1Stage2AdoptedResume.verifier.Reader.raw 4#usize r18 = ok (b18, r19) ∧
      lift (core.num.U32.from_le_bytes b18) = ok q18 ∧
      _root_.AspisR1Stage2AdoptedResume.verifier.Reader.raw 4#usize r19 = ok (b19, r20) ∧
      lift (core.num.U32.from_le_bytes b19) = ok q19 ∧
      _root_.AspisR1Stage2AdoptedResume.verifier.Reader.raw 4#usize r20 = ok (b20, r21) ∧
      lift (core.num.U32.from_le_bytes b20) = ok q20 ∧
      _root_.AspisR1Stage2AdoptedResume.verifier.Reader.raw 4#usize r21 = ok (b21, r22) ∧
      lift (core.num.U32.from_le_bytes b21) = ok q21 ∧
      validate_queries (Array.make 22#usize [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21]) =
        ok (core.result.Result.Ok queries) ∧
      r22.«at» = finalAt ∧ finalAt.val = cursor0.val + 88 := by
  unfold _root_.AspisR1Stage2AdoptedResume.verifier.resume_read_queries at h
  obtain ⟨b0, r1, hraw0, h⟩ := bind_pair_success _ _ _ h
  obtain ⟨q0, hdec0, h⟩ := bind_success _ _ _ h
  obtain ⟨b1, r2, hraw1, h⟩ := bind_pair_success _ _ _ h
  obtain ⟨q1, hdec1, h⟩ := bind_success _ _ _ h
  obtain ⟨b2, r3, hraw2, h⟩ := bind_pair_success _ _ _ h
  obtain ⟨q2, hdec2, h⟩ := bind_success _ _ _ h
  obtain ⟨b3, r4, hraw3, h⟩ := bind_pair_success _ _ _ h
  obtain ⟨q3, hdec3, h⟩ := bind_success _ _ _ h
  obtain ⟨b4, r5, hraw4, h⟩ := bind_pair_success _ _ _ h
  obtain ⟨q4, hdec4, h⟩ := bind_success _ _ _ h
  obtain ⟨b5, r6, hraw5, h⟩ := bind_pair_success _ _ _ h
  obtain ⟨q5, hdec5, h⟩ := bind_success _ _ _ h
  obtain ⟨b6, r7, hraw6, h⟩ := bind_pair_success _ _ _ h
  obtain ⟨q6, hdec6, h⟩ := bind_success _ _ _ h
  obtain ⟨b7, r8, hraw7, h⟩ := bind_pair_success _ _ _ h
  obtain ⟨q7, hdec7, h⟩ := bind_success _ _ _ h
  obtain ⟨b8, r9, hraw8, h⟩ := bind_pair_success _ _ _ h
  obtain ⟨q8, hdec8, h⟩ := bind_success _ _ _ h
  obtain ⟨b9, r10, hraw9, h⟩ := bind_pair_success _ _ _ h
  obtain ⟨q9, hdec9, h⟩ := bind_success _ _ _ h
  obtain ⟨b10, r11, hraw10, h⟩ := bind_pair_success _ _ _ h
  obtain ⟨q10, hdec10, h⟩ := bind_success _ _ _ h
  obtain ⟨b11, r12, hraw11, h⟩ := bind_pair_success _ _ _ h
  obtain ⟨q11, hdec11, h⟩ := bind_success _ _ _ h
  obtain ⟨b12, r13, hraw12, h⟩ := bind_pair_success _ _ _ h
  obtain ⟨q12, hdec12, h⟩ := bind_success _ _ _ h
  obtain ⟨b13, r14, hraw13, h⟩ := bind_pair_success _ _ _ h
  obtain ⟨q13, hdec13, h⟩ := bind_success _ _ _ h
  obtain ⟨b14, r15, hraw14, h⟩ := bind_pair_success _ _ _ h
  obtain ⟨q14, hdec14, h⟩ := bind_success _ _ _ h
  obtain ⟨b15, r16, hraw15, h⟩ := bind_pair_success _ _ _ h
  obtain ⟨q15, hdec15, h⟩ := bind_success _ _ _ h
  obtain ⟨b16, r17, hraw16, h⟩ := bind_pair_success _ _ _ h
  obtain ⟨q16, hdec16, h⟩ := bind_success _ _ _ h
  obtain ⟨b17, r18, hraw17, h⟩ := bind_pair_success _ _ _ h
  obtain ⟨q17, hdec17, h⟩ := bind_success _ _ _ h
  obtain ⟨b18, r19, hraw18, h⟩ := bind_pair_success _ _ _ h
  obtain ⟨q18, hdec18, h⟩ := bind_success _ _ _ h
  obtain ⟨b19, r20, hraw19, h⟩ := bind_pair_success _ _ _ h
  obtain ⟨q19, hdec19, h⟩ := bind_success _ _ _ h
  obtain ⟨b20, r21, hraw20, h⟩ := bind_pair_success _ _ _ h
  obtain ⟨q20, hdec20, h⟩ := bind_success _ _ _ h
  obtain ⟨b21, r22, hraw21, h⟩ := bind_pair_success _ _ _ h
  obtain ⟨q21, hdec21, h⟩ := bind_success _ _ _ h
  obtain ⟨checked, hcall, h⟩ := bind_success _ _ _ h
  have hvalid : checked = core.result.Result.Ok queries ∧ r22.«at» = finalAt := by
    cases checked with
    | Err err =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from] at h
        cases h
    | Ok out =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
        simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨hout, hcursor⟩
        exact ⟨congrArg core.result.Result.Ok hout, hcursor⟩
  rcases hvalid with ⟨hchecked, hcursor⟩
  have hcall' : validate_queries
      (Array.make 22#usize [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10,
        q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21]) =
      ok (core.result.Result.Ok queries) := by
    rw [hchecked] at hcall
    exact hcall
  let r0 : _root_.AspisR1Stage2AdoptedResume.verifier.Reader := { bytes, «at» := cursor0 }
  have hstep0 : r1.«at».val = r0.«at».val + 4 := by
    exact AspisR1Stage2AdoptedReader.RawCursorAdvanceNat.raw_success_advances_value 4#usize r0 b0 r1 hraw0
  have hstep1 : r2.«at».val = r1.«at».val + 4 := by
    exact AspisR1Stage2AdoptedReader.RawCursorAdvanceNat.raw_success_advances_value 4#usize r1 b1 r2 hraw1
  have hstep2 : r3.«at».val = r2.«at».val + 4 := by
    exact AspisR1Stage2AdoptedReader.RawCursorAdvanceNat.raw_success_advances_value 4#usize r2 b2 r3 hraw2
  have hstep3 : r4.«at».val = r3.«at».val + 4 := by
    exact AspisR1Stage2AdoptedReader.RawCursorAdvanceNat.raw_success_advances_value 4#usize r3 b3 r4 hraw3
  have hstep4 : r5.«at».val = r4.«at».val + 4 := by
    exact AspisR1Stage2AdoptedReader.RawCursorAdvanceNat.raw_success_advances_value 4#usize r4 b4 r5 hraw4
  have hstep5 : r6.«at».val = r5.«at».val + 4 := by
    exact AspisR1Stage2AdoptedReader.RawCursorAdvanceNat.raw_success_advances_value 4#usize r5 b5 r6 hraw5
  have hstep6 : r7.«at».val = r6.«at».val + 4 := by
    exact AspisR1Stage2AdoptedReader.RawCursorAdvanceNat.raw_success_advances_value 4#usize r6 b6 r7 hraw6
  have hstep7 : r8.«at».val = r7.«at».val + 4 := by
    exact AspisR1Stage2AdoptedReader.RawCursorAdvanceNat.raw_success_advances_value 4#usize r7 b7 r8 hraw7
  have hstep8 : r9.«at».val = r8.«at».val + 4 := by
    exact AspisR1Stage2AdoptedReader.RawCursorAdvanceNat.raw_success_advances_value 4#usize r8 b8 r9 hraw8
  have hstep9 : r10.«at».val = r9.«at».val + 4 := by
    exact AspisR1Stage2AdoptedReader.RawCursorAdvanceNat.raw_success_advances_value 4#usize r9 b9 r10 hraw9
  have hstep10 : r11.«at».val = r10.«at».val + 4 := by
    exact AspisR1Stage2AdoptedReader.RawCursorAdvanceNat.raw_success_advances_value 4#usize r10 b10 r11 hraw10
  have hstep11 : r12.«at».val = r11.«at».val + 4 := by
    exact AspisR1Stage2AdoptedReader.RawCursorAdvanceNat.raw_success_advances_value 4#usize r11 b11 r12 hraw11
  have hstep12 : r13.«at».val = r12.«at».val + 4 := by
    exact AspisR1Stage2AdoptedReader.RawCursorAdvanceNat.raw_success_advances_value 4#usize r12 b12 r13 hraw12
  have hstep13 : r14.«at».val = r13.«at».val + 4 := by
    exact AspisR1Stage2AdoptedReader.RawCursorAdvanceNat.raw_success_advances_value 4#usize r13 b13 r14 hraw13
  have hstep14 : r15.«at».val = r14.«at».val + 4 := by
    exact AspisR1Stage2AdoptedReader.RawCursorAdvanceNat.raw_success_advances_value 4#usize r14 b14 r15 hraw14
  have hstep15 : r16.«at».val = r15.«at».val + 4 := by
    exact AspisR1Stage2AdoptedReader.RawCursorAdvanceNat.raw_success_advances_value 4#usize r15 b15 r16 hraw15
  have hstep16 : r17.«at».val = r16.«at».val + 4 := by
    exact AspisR1Stage2AdoptedReader.RawCursorAdvanceNat.raw_success_advances_value 4#usize r16 b16 r17 hraw16
  have hstep17 : r18.«at».val = r17.«at».val + 4 := by
    exact AspisR1Stage2AdoptedReader.RawCursorAdvanceNat.raw_success_advances_value 4#usize r17 b17 r18 hraw17
  have hstep18 : r19.«at».val = r18.«at».val + 4 := by
    exact AspisR1Stage2AdoptedReader.RawCursorAdvanceNat.raw_success_advances_value 4#usize r18 b18 r19 hraw18
  have hstep19 : r20.«at».val = r19.«at».val + 4 := by
    exact AspisR1Stage2AdoptedReader.RawCursorAdvanceNat.raw_success_advances_value 4#usize r19 b19 r20 hraw19
  have hstep20 : r21.«at».val = r20.«at».val + 4 := by
    exact AspisR1Stage2AdoptedReader.RawCursorAdvanceNat.raw_success_advances_value 4#usize r20 b20 r21 hraw20
  have hstep21 : r22.«at».val = r21.«at».val + 4 := by
    exact AspisR1Stage2AdoptedReader.RawCursorAdvanceNat.raw_success_advances_value 4#usize r21 b21 r22 hraw21
  have hchain := AspisR1Stage2AdoptedReader.QueryCursorNatChain.nat_add_four_chain_22
    cursor0.val r1.«at».val r2.«at».val r3.«at».val r4.«at».val r5.«at».val r6.«at».val r7.«at».val r8.«at».val r9.«at».val r10.«at».val r11.«at».val r12.«at».val r13.«at».val r14.«at».val r15.«at».val r16.«at».val r17.«at».val r18.«at».val r19.«at».val r20.«at».val r21.«at».val r22.«at».val
    hstep0 hstep1 hstep2 hstep3 hstep4 hstep5 hstep6 hstep7 hstep8 hstep9 hstep10 hstep11 hstep12 hstep13 hstep14 hstep15 hstep16 hstep17 hstep18 hstep19 hstep20 hstep21
  have hcursorVal : r22.«at».val = finalAt.val :=
    congrArg (fun x : Usize => x.val) hcursor
  have hadvance : finalAt.val = cursor0.val + 88 := by
    rw [← hcursorVal]
    exact hchain
  exact ⟨r1, b0, q0, r2, b1, q1, r3, b2, q2, r4, b3, q3, r5, b4, q4,
    r6, b5, q5, r7, b6, q6, r8, b7, q7, r9, b8, q8, r10, b9, q9,
    r11, b10, q10, r12, b11, q11, r13, b12, q12, r14, b13, q13,
    r15, b14, q14, r16, b15, q15, r17, b16, q16, r18, b17, q17,
    r19, b18, q18, r20, b19, q19, r21, b20, q20, r22, b21, q21,
    hraw0, hdec0, hraw1, hdec1, hraw2, hdec2, hraw3, hdec3, hraw4, hdec4,
    hraw5, hdec5, hraw6, hdec6, hraw7, hdec7, hraw8, hdec8, hraw9, hdec9,
    hraw10, hdec10, hraw11, hdec11, hraw12, hdec12, hraw13, hdec13, hraw14,
    hdec14, hraw15, hdec15, hraw16, hdec16, hraw17, hdec17, hraw18, hdec18,
    hraw19, hdec19, hraw20, hdec20, hraw21, hdec21, hcall', hcursor, hadvance⟩

#print axioms successful_query_read_exposes_validation_call

end AspisR1Stage2AdoptedReader.QueryReaderSuccess
