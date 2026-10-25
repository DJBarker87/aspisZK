import Port6CK_Queries
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_QueryFrame
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem reached (r out : verifier.Reader) (q : Array U32 22#usize)
    (room : r.at.val+88≤r.bytes.val.length)
    (actual : Port6CK_Queries.read CheckpointBytes3Reader.raw r=ok (q,out)) :
    out.at.val=r.at.val+88 ∧ out.bytes=r.bytes := by
  unfold Port6CK_Queries.read at actual
  obtain ⟨⟨b0,r1⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r r1 b0
    (by change r.at.val+4≤r.bytes.val.length; omega) called
  change r1.at.val=r.at.val+4 at cursor
  have room : r1.at.val+84≤r1.bytes.val.length := by rw [cursor,backing]; omega
  have cursor0 : r1.at.val=r.at.val+4 := by omega
  have backing0 : r1.bytes=r.bytes := by first | exact backing | exact backing.trans backing-1
  simp only [Aeneas.Std.uncurry] at actual
  obtain ⟨q0,decoded,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨⟨b1,r2⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r1 r2 b1
    (by change r1.at.val+4≤r1.bytes.val.length; omega) called
  change r2.at.val=r1.at.val+4 at cursor
  have room : r2.at.val+80≤r2.bytes.val.length := by rw [cursor,backing]; omega
  have cursor1 : r2.at.val=r.at.val+8 := by omega
  have backing1 : r2.bytes=r.bytes := by first | exact backing | exact backing.trans backing0
  simp only [Aeneas.Std.uncurry] at actual
  obtain ⟨q1,decoded,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨⟨b2,r3⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r2 r3 b2
    (by change r2.at.val+4≤r2.bytes.val.length; omega) called
  change r3.at.val=r2.at.val+4 at cursor
  have room : r3.at.val+76≤r3.bytes.val.length := by rw [cursor,backing]; omega
  have cursor2 : r3.at.val=r.at.val+12 := by omega
  have backing2 : r3.bytes=r.bytes := by first | exact backing | exact backing.trans backing1
  simp only [Aeneas.Std.uncurry] at actual
  obtain ⟨q2,decoded,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨⟨b3,r4⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r3 r4 b3
    (by change r3.at.val+4≤r3.bytes.val.length; omega) called
  change r4.at.val=r3.at.val+4 at cursor
  have room : r4.at.val+72≤r4.bytes.val.length := by rw [cursor,backing]; omega
  have cursor3 : r4.at.val=r.at.val+16 := by omega
  have backing3 : r4.bytes=r.bytes := by first | exact backing | exact backing.trans backing2
  simp only [Aeneas.Std.uncurry] at actual
  obtain ⟨q3,decoded,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨⟨b4,r5⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r4 r5 b4
    (by change r4.at.val+4≤r4.bytes.val.length; omega) called
  change r5.at.val=r4.at.val+4 at cursor
  have room : r5.at.val+68≤r5.bytes.val.length := by rw [cursor,backing]; omega
  have cursor4 : r5.at.val=r.at.val+20 := by omega
  have backing4 : r5.bytes=r.bytes := by first | exact backing | exact backing.trans backing3
  simp only [Aeneas.Std.uncurry] at actual
  obtain ⟨q4,decoded,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨⟨b5,r6⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r5 r6 b5
    (by change r5.at.val+4≤r5.bytes.val.length; omega) called
  change r6.at.val=r5.at.val+4 at cursor
  have room : r6.at.val+64≤r6.bytes.val.length := by rw [cursor,backing]; omega
  have cursor5 : r6.at.val=r.at.val+24 := by omega
  have backing5 : r6.bytes=r.bytes := by first | exact backing | exact backing.trans backing4
  simp only [Aeneas.Std.uncurry] at actual
  obtain ⟨q5,decoded,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨⟨b6,r7⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r6 r7 b6
    (by change r6.at.val+4≤r6.bytes.val.length; omega) called
  change r7.at.val=r6.at.val+4 at cursor
  have room : r7.at.val+60≤r7.bytes.val.length := by rw [cursor,backing]; omega
  have cursor6 : r7.at.val=r.at.val+28 := by omega
  have backing6 : r7.bytes=r.bytes := by first | exact backing | exact backing.trans backing5
  simp only [Aeneas.Std.uncurry] at actual
  obtain ⟨q6,decoded,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨⟨b7,r8⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r7 r8 b7
    (by change r7.at.val+4≤r7.bytes.val.length; omega) called
  change r8.at.val=r7.at.val+4 at cursor
  have room : r8.at.val+56≤r8.bytes.val.length := by rw [cursor,backing]; omega
  have cursor7 : r8.at.val=r.at.val+32 := by omega
  have backing7 : r8.bytes=r.bytes := by first | exact backing | exact backing.trans backing6
  simp only [Aeneas.Std.uncurry] at actual
  obtain ⟨q7,decoded,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨⟨b8,r9⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r8 r9 b8
    (by change r8.at.val+4≤r8.bytes.val.length; omega) called
  change r9.at.val=r8.at.val+4 at cursor
  have room : r9.at.val+52≤r9.bytes.val.length := by rw [cursor,backing]; omega
  have cursor8 : r9.at.val=r.at.val+36 := by omega
  have backing8 : r9.bytes=r.bytes := by first | exact backing | exact backing.trans backing7
  simp only [Aeneas.Std.uncurry] at actual
  obtain ⟨q8,decoded,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨⟨b9,r10⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r9 r10 b9
    (by change r9.at.val+4≤r9.bytes.val.length; omega) called
  change r10.at.val=r9.at.val+4 at cursor
  have room : r10.at.val+48≤r10.bytes.val.length := by rw [cursor,backing]; omega
  have cursor9 : r10.at.val=r.at.val+40 := by omega
  have backing9 : r10.bytes=r.bytes := by first | exact backing | exact backing.trans backing8
  simp only [Aeneas.Std.uncurry] at actual
  obtain ⟨q9,decoded,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨⟨b10,r11⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r10 r11 b10
    (by change r10.at.val+4≤r10.bytes.val.length; omega) called
  change r11.at.val=r10.at.val+4 at cursor
  have room : r11.at.val+44≤r11.bytes.val.length := by rw [cursor,backing]; omega
  have cursor10 : r11.at.val=r.at.val+44 := by omega
  have backing10 : r11.bytes=r.bytes := by first | exact backing | exact backing.trans backing9
  simp only [Aeneas.Std.uncurry] at actual
  obtain ⟨q10,decoded,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨⟨b11,r12⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r11 r12 b11
    (by change r11.at.val+4≤r11.bytes.val.length; omega) called
  change r12.at.val=r11.at.val+4 at cursor
  have room : r12.at.val+40≤r12.bytes.val.length := by rw [cursor,backing]; omega
  have cursor11 : r12.at.val=r.at.val+48 := by omega
  have backing11 : r12.bytes=r.bytes := by first | exact backing | exact backing.trans backing10
  simp only [Aeneas.Std.uncurry] at actual
  obtain ⟨q11,decoded,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨⟨b12,r13⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r12 r13 b12
    (by change r12.at.val+4≤r12.bytes.val.length; omega) called
  change r13.at.val=r12.at.val+4 at cursor
  have room : r13.at.val+36≤r13.bytes.val.length := by rw [cursor,backing]; omega
  have cursor12 : r13.at.val=r.at.val+52 := by omega
  have backing12 : r13.bytes=r.bytes := by first | exact backing | exact backing.trans backing11
  simp only [Aeneas.Std.uncurry] at actual
  obtain ⟨q12,decoded,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨⟨b13,r14⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r13 r14 b13
    (by change r13.at.val+4≤r13.bytes.val.length; omega) called
  change r14.at.val=r13.at.val+4 at cursor
  have room : r14.at.val+32≤r14.bytes.val.length := by rw [cursor,backing]; omega
  have cursor13 : r14.at.val=r.at.val+56 := by omega
  have backing13 : r14.bytes=r.bytes := by first | exact backing | exact backing.trans backing12
  simp only [Aeneas.Std.uncurry] at actual
  obtain ⟨q13,decoded,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨⟨b14,r15⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r14 r15 b14
    (by change r14.at.val+4≤r14.bytes.val.length; omega) called
  change r15.at.val=r14.at.val+4 at cursor
  have room : r15.at.val+28≤r15.bytes.val.length := by rw [cursor,backing]; omega
  have cursor14 : r15.at.val=r.at.val+60 := by omega
  have backing14 : r15.bytes=r.bytes := by first | exact backing | exact backing.trans backing13
  simp only [Aeneas.Std.uncurry] at actual
  obtain ⟨q14,decoded,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨⟨b15,r16⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r15 r16 b15
    (by change r15.at.val+4≤r15.bytes.val.length; omega) called
  change r16.at.val=r15.at.val+4 at cursor
  have room : r16.at.val+24≤r16.bytes.val.length := by rw [cursor,backing]; omega
  have cursor15 : r16.at.val=r.at.val+64 := by omega
  have backing15 : r16.bytes=r.bytes := by first | exact backing | exact backing.trans backing14
  simp only [Aeneas.Std.uncurry] at actual
  obtain ⟨q15,decoded,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨⟨b16,r17⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r16 r17 b16
    (by change r16.at.val+4≤r16.bytes.val.length; omega) called
  change r17.at.val=r16.at.val+4 at cursor
  have room : r17.at.val+20≤r17.bytes.val.length := by rw [cursor,backing]; omega
  have cursor16 : r17.at.val=r.at.val+68 := by omega
  have backing16 : r17.bytes=r.bytes := by first | exact backing | exact backing.trans backing15
  simp only [Aeneas.Std.uncurry] at actual
  obtain ⟨q16,decoded,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨⟨b17,r18⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r17 r18 b17
    (by change r17.at.val+4≤r17.bytes.val.length; omega) called
  change r18.at.val=r17.at.val+4 at cursor
  have room : r18.at.val+16≤r18.bytes.val.length := by rw [cursor,backing]; omega
  have cursor17 : r18.at.val=r.at.val+72 := by omega
  have backing17 : r18.bytes=r.bytes := by first | exact backing | exact backing.trans backing16
  simp only [Aeneas.Std.uncurry] at actual
  obtain ⟨q17,decoded,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨⟨b18,r19⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r18 r19 b18
    (by change r18.at.val+4≤r18.bytes.val.length; omega) called
  change r19.at.val=r18.at.val+4 at cursor
  have room : r19.at.val+12≤r19.bytes.val.length := by rw [cursor,backing]; omega
  have cursor18 : r19.at.val=r.at.val+76 := by omega
  have backing18 : r19.bytes=r.bytes := by first | exact backing | exact backing.trans backing17
  simp only [Aeneas.Std.uncurry] at actual
  obtain ⟨q18,decoded,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨⟨b19,r20⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r19 r20 b19
    (by change r19.at.val+4≤r19.bytes.val.length; omega) called
  change r20.at.val=r19.at.val+4 at cursor
  have room : r20.at.val+8≤r20.bytes.val.length := by rw [cursor,backing]; omega
  have cursor19 : r20.at.val=r.at.val+80 := by omega
  have backing19 : r20.bytes=r.bytes := by first | exact backing | exact backing.trans backing18
  simp only [Aeneas.Std.uncurry] at actual
  obtain ⟨q19,decoded,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨⟨b20,r21⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r20 r21 b20
    (by change r20.at.val+4≤r20.bytes.val.length; omega) called
  change r21.at.val=r20.at.val+4 at cursor
  have room : r21.at.val+4≤r21.bytes.val.length := by rw [cursor,backing]; omega
  have cursor20 : r21.at.val=r.at.val+84 := by omega
  have backing20 : r21.bytes=r.bytes := by first | exact backing | exact backing.trans backing19
  simp only [Aeneas.Std.uncurry] at actual
  obtain ⟨q20,decoded,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨⟨b21,r22⟩,called,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  obtain ⟨contents,cursor,backing⟩ := CheckpointBytes4RawFields.raw_success 4#usize r21 r22 b21
    (by change r21.at.val+4≤r21.bytes.val.length; omega) called
  change r22.at.val=r21.at.val+4 at cursor
  have room : r22.at.val+0≤r22.bytes.val.length := by rw [cursor,backing]; omega
  have cursor21 : r22.at.val=r.at.val+88 := by omega
  have backing21 : r22.bytes=r.bytes := by first | exact backing | exact backing.trans backing20
  simp only [Aeneas.Std.uncurry] at actual
  obtain ⟨q21,decoded,actual⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  have finalReader := congrArg Prod.snd (Result.ok.inj actual)
  dsimp only at finalReader
  subst out
  exact ⟨cursor21,backing21⟩

#print axioms reached
end AspisR1.Port6CK_QueryFrame
end
