import Port6CK_Roots
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_Queries
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port6CK_Roots (Raw)
def read (raw : Raw) (r : verifier.Reader) : Result (Array U32 22#usize × verifier.Reader) := do
  let (b0,r1) ← raw 4#usize r
  let q0 ← lift (core.num.U32.from_le_bytes b0)
  let (b1,r2) ← raw 4#usize r1
  let q1 ← lift (core.num.U32.from_le_bytes b1)
  let (b2,r3) ← raw 4#usize r2
  let q2 ← lift (core.num.U32.from_le_bytes b2)
  let (b3,r4) ← raw 4#usize r3
  let q3 ← lift (core.num.U32.from_le_bytes b3)
  let (b4,r5) ← raw 4#usize r4
  let q4 ← lift (core.num.U32.from_le_bytes b4)
  let (b5,r6) ← raw 4#usize r5
  let q5 ← lift (core.num.U32.from_le_bytes b5)
  let (b6,r7) ← raw 4#usize r6
  let q6 ← lift (core.num.U32.from_le_bytes b6)
  let (b7,r8) ← raw 4#usize r7
  let q7 ← lift (core.num.U32.from_le_bytes b7)
  let (b8,r9) ← raw 4#usize r8
  let q8 ← lift (core.num.U32.from_le_bytes b8)
  let (b9,r10) ← raw 4#usize r9
  let q9 ← lift (core.num.U32.from_le_bytes b9)
  let (b10,r11) ← raw 4#usize r10
  let q10 ← lift (core.num.U32.from_le_bytes b10)
  let (b11,r12) ← raw 4#usize r11
  let q11 ← lift (core.num.U32.from_le_bytes b11)
  let (b12,r13) ← raw 4#usize r12
  let q12 ← lift (core.num.U32.from_le_bytes b12)
  let (b13,r14) ← raw 4#usize r13
  let q13 ← lift (core.num.U32.from_le_bytes b13)
  let (b14,r15) ← raw 4#usize r14
  let q14 ← lift (core.num.U32.from_le_bytes b14)
  let (b15,r16) ← raw 4#usize r15
  let q15 ← lift (core.num.U32.from_le_bytes b15)
  let (b16,r17) ← raw 4#usize r16
  let q16 ← lift (core.num.U32.from_le_bytes b16)
  let (b17,r18) ← raw 4#usize r17
  let q17 ← lift (core.num.U32.from_le_bytes b17)
  let (b18,r19) ← raw 4#usize r18
  let q18 ← lift (core.num.U32.from_le_bytes b18)
  let (b19,r20) ← raw 4#usize r19
  let q19 ← lift (core.num.U32.from_le_bytes b19)
  let (b20,r21) ← raw 4#usize r20
  let q20 ← lift (core.num.U32.from_le_bytes b20)
  let (b21,r22) ← raw 4#usize r21
  let q21 ← lift (core.num.U32.from_le_bytes b21)
  ok (Array.make 22#usize [q0,q1,q2,q3,q4,q5,q6,q7,q8,q9,q10,q11,q12,q13,q14,q15,q16,q17,q18,q19,q20,q21],r22)

theorem reference
    (unwrap : (N : Usize) → core.result.Result (Array U8 N) core.array.TryFromSliceError → Result (Array U8 N))
    (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b)
    (r : verifier.Reader) (room : r.at.val+88≤r.bytes.val.length) (size : r.bytes.val.length≤4096) :
    read (fun N => Port5Q2_ReaderRaw.raw N (unwrap N)) r =
      read CheckpointBytes3Reader.raw r := by
  unfold read
  dsimp only
  rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) r (by change r.at.val+4≤r.bytes.val.length; omega) (by omega)]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair called
  rcases pair with ⟨b0,r1⟩
  simp only [Aeneas.Std.uncurry]
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r r1 b0 (by change r.at.val+4≤r.bytes.val.length; omega) called
  change r1.at.val=r.at.val+4 at cursor
  have room : r1.at.val+84≤r1.bytes.val.length := by rw [cursor,backing]; omega
  have size : r1.bytes.val.length≤4096 := by rw [backing]; omega
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro query decoded
  rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) r1 (by change r1.at.val+4≤r1.bytes.val.length; omega) (by omega)]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair called
  rcases pair with ⟨b1,r2⟩
  simp only [Aeneas.Std.uncurry]
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r1 r2 b1 (by change r1.at.val+4≤r1.bytes.val.length; omega) called
  change r2.at.val=r1.at.val+4 at cursor
  have room : r2.at.val+80≤r2.bytes.val.length := by rw [cursor,backing]; omega
  have size : r2.bytes.val.length≤4096 := by rw [backing]; omega
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro query decoded
  rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) r2 (by change r2.at.val+4≤r2.bytes.val.length; omega) (by omega)]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair called
  rcases pair with ⟨b2,r3⟩
  simp only [Aeneas.Std.uncurry]
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r2 r3 b2 (by change r2.at.val+4≤r2.bytes.val.length; omega) called
  change r3.at.val=r2.at.val+4 at cursor
  have room : r3.at.val+76≤r3.bytes.val.length := by rw [cursor,backing]; omega
  have size : r3.bytes.val.length≤4096 := by rw [backing]; omega
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro query decoded
  rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) r3 (by change r3.at.val+4≤r3.bytes.val.length; omega) (by omega)]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair called
  rcases pair with ⟨b3,r4⟩
  simp only [Aeneas.Std.uncurry]
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r3 r4 b3 (by change r3.at.val+4≤r3.bytes.val.length; omega) called
  change r4.at.val=r3.at.val+4 at cursor
  have room : r4.at.val+72≤r4.bytes.val.length := by rw [cursor,backing]; omega
  have size : r4.bytes.val.length≤4096 := by rw [backing]; omega
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro query decoded
  rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) r4 (by change r4.at.val+4≤r4.bytes.val.length; omega) (by omega)]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair called
  rcases pair with ⟨b4,r5⟩
  simp only [Aeneas.Std.uncurry]
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r4 r5 b4 (by change r4.at.val+4≤r4.bytes.val.length; omega) called
  change r5.at.val=r4.at.val+4 at cursor
  have room : r5.at.val+68≤r5.bytes.val.length := by rw [cursor,backing]; omega
  have size : r5.bytes.val.length≤4096 := by rw [backing]; omega
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro query decoded
  rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) r5 (by change r5.at.val+4≤r5.bytes.val.length; omega) (by omega)]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair called
  rcases pair with ⟨b5,r6⟩
  simp only [Aeneas.Std.uncurry]
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r5 r6 b5 (by change r5.at.val+4≤r5.bytes.val.length; omega) called
  change r6.at.val=r5.at.val+4 at cursor
  have room : r6.at.val+64≤r6.bytes.val.length := by rw [cursor,backing]; omega
  have size : r6.bytes.val.length≤4096 := by rw [backing]; omega
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro query decoded
  rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) r6 (by change r6.at.val+4≤r6.bytes.val.length; omega) (by omega)]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair called
  rcases pair with ⟨b6,r7⟩
  simp only [Aeneas.Std.uncurry]
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r6 r7 b6 (by change r6.at.val+4≤r6.bytes.val.length; omega) called
  change r7.at.val=r6.at.val+4 at cursor
  have room : r7.at.val+60≤r7.bytes.val.length := by rw [cursor,backing]; omega
  have size : r7.bytes.val.length≤4096 := by rw [backing]; omega
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro query decoded
  rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) r7 (by change r7.at.val+4≤r7.bytes.val.length; omega) (by omega)]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair called
  rcases pair with ⟨b7,r8⟩
  simp only [Aeneas.Std.uncurry]
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r7 r8 b7 (by change r7.at.val+4≤r7.bytes.val.length; omega) called
  change r8.at.val=r7.at.val+4 at cursor
  have room : r8.at.val+56≤r8.bytes.val.length := by rw [cursor,backing]; omega
  have size : r8.bytes.val.length≤4096 := by rw [backing]; omega
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro query decoded
  rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) r8 (by change r8.at.val+4≤r8.bytes.val.length; omega) (by omega)]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair called
  rcases pair with ⟨b8,r9⟩
  simp only [Aeneas.Std.uncurry]
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r8 r9 b8 (by change r8.at.val+4≤r8.bytes.val.length; omega) called
  change r9.at.val=r8.at.val+4 at cursor
  have room : r9.at.val+52≤r9.bytes.val.length := by rw [cursor,backing]; omega
  have size : r9.bytes.val.length≤4096 := by rw [backing]; omega
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro query decoded
  rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) r9 (by change r9.at.val+4≤r9.bytes.val.length; omega) (by omega)]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair called
  rcases pair with ⟨b9,r10⟩
  simp only [Aeneas.Std.uncurry]
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r9 r10 b9 (by change r9.at.val+4≤r9.bytes.val.length; omega) called
  change r10.at.val=r9.at.val+4 at cursor
  have room : r10.at.val+48≤r10.bytes.val.length := by rw [cursor,backing]; omega
  have size : r10.bytes.val.length≤4096 := by rw [backing]; omega
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro query decoded
  rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) r10 (by change r10.at.val+4≤r10.bytes.val.length; omega) (by omega)]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair called
  rcases pair with ⟨b10,r11⟩
  simp only [Aeneas.Std.uncurry]
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r10 r11 b10 (by change r10.at.val+4≤r10.bytes.val.length; omega) called
  change r11.at.val=r10.at.val+4 at cursor
  have room : r11.at.val+44≤r11.bytes.val.length := by rw [cursor,backing]; omega
  have size : r11.bytes.val.length≤4096 := by rw [backing]; omega
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro query decoded
  rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) r11 (by change r11.at.val+4≤r11.bytes.val.length; omega) (by omega)]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair called
  rcases pair with ⟨b11,r12⟩
  simp only [Aeneas.Std.uncurry]
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r11 r12 b11 (by change r11.at.val+4≤r11.bytes.val.length; omega) called
  change r12.at.val=r11.at.val+4 at cursor
  have room : r12.at.val+40≤r12.bytes.val.length := by rw [cursor,backing]; omega
  have size : r12.bytes.val.length≤4096 := by rw [backing]; omega
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro query decoded
  rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) r12 (by change r12.at.val+4≤r12.bytes.val.length; omega) (by omega)]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair called
  rcases pair with ⟨b12,r13⟩
  simp only [Aeneas.Std.uncurry]
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r12 r13 b12 (by change r12.at.val+4≤r12.bytes.val.length; omega) called
  change r13.at.val=r12.at.val+4 at cursor
  have room : r13.at.val+36≤r13.bytes.val.length := by rw [cursor,backing]; omega
  have size : r13.bytes.val.length≤4096 := by rw [backing]; omega
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro query decoded
  rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) r13 (by change r13.at.val+4≤r13.bytes.val.length; omega) (by omega)]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair called
  rcases pair with ⟨b13,r14⟩
  simp only [Aeneas.Std.uncurry]
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r13 r14 b13 (by change r13.at.val+4≤r13.bytes.val.length; omega) called
  change r14.at.val=r13.at.val+4 at cursor
  have room : r14.at.val+32≤r14.bytes.val.length := by rw [cursor,backing]; omega
  have size : r14.bytes.val.length≤4096 := by rw [backing]; omega
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro query decoded
  rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) r14 (by change r14.at.val+4≤r14.bytes.val.length; omega) (by omega)]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair called
  rcases pair with ⟨b14,r15⟩
  simp only [Aeneas.Std.uncurry]
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r14 r15 b14 (by change r14.at.val+4≤r14.bytes.val.length; omega) called
  change r15.at.val=r14.at.val+4 at cursor
  have room : r15.at.val+28≤r15.bytes.val.length := by rw [cursor,backing]; omega
  have size : r15.bytes.val.length≤4096 := by rw [backing]; omega
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro query decoded
  rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) r15 (by change r15.at.val+4≤r15.bytes.val.length; omega) (by omega)]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair called
  rcases pair with ⟨b15,r16⟩
  simp only [Aeneas.Std.uncurry]
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r15 r16 b15 (by change r15.at.val+4≤r15.bytes.val.length; omega) called
  change r16.at.val=r15.at.val+4 at cursor
  have room : r16.at.val+24≤r16.bytes.val.length := by rw [cursor,backing]; omega
  have size : r16.bytes.val.length≤4096 := by rw [backing]; omega
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro query decoded
  rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) r16 (by change r16.at.val+4≤r16.bytes.val.length; omega) (by omega)]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair called
  rcases pair with ⟨b16,r17⟩
  simp only [Aeneas.Std.uncurry]
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r16 r17 b16 (by change r16.at.val+4≤r16.bytes.val.length; omega) called
  change r17.at.val=r16.at.val+4 at cursor
  have room : r17.at.val+20≤r17.bytes.val.length := by rw [cursor,backing]; omega
  have size : r17.bytes.val.length≤4096 := by rw [backing]; omega
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro query decoded
  rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) r17 (by change r17.at.val+4≤r17.bytes.val.length; omega) (by omega)]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair called
  rcases pair with ⟨b17,r18⟩
  simp only [Aeneas.Std.uncurry]
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r17 r18 b17 (by change r17.at.val+4≤r17.bytes.val.length; omega) called
  change r18.at.val=r17.at.val+4 at cursor
  have room : r18.at.val+16≤r18.bytes.val.length := by rw [cursor,backing]; omega
  have size : r18.bytes.val.length≤4096 := by rw [backing]; omega
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro query decoded
  rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) r18 (by change r18.at.val+4≤r18.bytes.val.length; omega) (by omega)]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair called
  rcases pair with ⟨b18,r19⟩
  simp only [Aeneas.Std.uncurry]
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r18 r19 b18 (by change r18.at.val+4≤r18.bytes.val.length; omega) called
  change r19.at.val=r18.at.val+4 at cursor
  have room : r19.at.val+12≤r19.bytes.val.length := by rw [cursor,backing]; omega
  have size : r19.bytes.val.length≤4096 := by rw [backing]; omega
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro query decoded
  rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) r19 (by change r19.at.val+4≤r19.bytes.val.length; omega) (by omega)]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair called
  rcases pair with ⟨b19,r20⟩
  simp only [Aeneas.Std.uncurry]
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r19 r20 b19 (by change r19.at.val+4≤r19.bytes.val.length; omega) called
  change r20.at.val=r19.at.val+4 at cursor
  have room : r20.at.val+8≤r20.bytes.val.length := by rw [cursor,backing]; omega
  have size : r20.bytes.val.length≤4096 := by rw [backing]; omega
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro query decoded
  rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) r20 (by change r20.at.val+4≤r20.bytes.val.length; omega) (by omega)]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro pair called
  rcases pair with ⟨b20,r21⟩
  simp only [Aeneas.Std.uncurry]
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r20 r21 b20 (by change r20.at.val+4≤r20.bytes.val.length; omega) called
  change r21.at.val=r20.at.val+4 at cursor
  have room : r21.at.val+4≤r21.bytes.val.length := by rw [cursor,backing]; omega
  have size : r21.bytes.val.length≤4096 := by rw [backing]; omega
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro query decoded
  rw [Port5Q2_ReaderRaw.reference 4#usize (unwrap _) (unwrap_ok _) r21 (by change r21.at.val+4≤r21.bytes.val.length; omega) (by omega)]

#print axioms reference
end AspisR1.Port6CK_Queries
end
