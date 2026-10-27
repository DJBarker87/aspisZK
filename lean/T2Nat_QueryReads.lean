import T2Nat_Try
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_QueryReads
open Aeneas Aeneas.Std Result AspisR1Stage2
open T2Nat_ResultEq
abbrev Raw := Port5Q2_ReaderScalar.Raw

def queries (raw : Raw) (r : verifier.Reader) :
    Result (Array U32 22#usize × verifier.Reader) := do
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

theorem congr (left right : Raw)
    (same : ∀ N r, EqOk (left N r) (right N r)) (r : verifier.Reader) :
    EqOk (queries left r) (queries right r) := by
  unfold queries
  apply T2Nat_ResultEq.bind (same _ _)
  rintro ⟨b0,r0⟩
  apply T2Nat_ResultEq.bind (T2Nat_ResultEq.refl _)
  intro q0
  apply T2Nat_ResultEq.bind (same _ _)
  rintro ⟨b1,r1⟩
  apply T2Nat_ResultEq.bind (T2Nat_ResultEq.refl _)
  intro q1
  apply T2Nat_ResultEq.bind (same _ _)
  rintro ⟨b2,r2⟩
  apply T2Nat_ResultEq.bind (T2Nat_ResultEq.refl _)
  intro q2
  apply T2Nat_ResultEq.bind (same _ _)
  rintro ⟨b3,r3⟩
  apply T2Nat_ResultEq.bind (T2Nat_ResultEq.refl _)
  intro q3
  apply T2Nat_ResultEq.bind (same _ _)
  rintro ⟨b4,r4⟩
  apply T2Nat_ResultEq.bind (T2Nat_ResultEq.refl _)
  intro q4
  apply T2Nat_ResultEq.bind (same _ _)
  rintro ⟨b5,r5⟩
  apply T2Nat_ResultEq.bind (T2Nat_ResultEq.refl _)
  intro q5
  apply T2Nat_ResultEq.bind (same _ _)
  rintro ⟨b6,r6⟩
  apply T2Nat_ResultEq.bind (T2Nat_ResultEq.refl _)
  intro q6
  apply T2Nat_ResultEq.bind (same _ _)
  rintro ⟨b7,r7⟩
  apply T2Nat_ResultEq.bind (T2Nat_ResultEq.refl _)
  intro q7
  apply T2Nat_ResultEq.bind (same _ _)
  rintro ⟨b8,r8⟩
  apply T2Nat_ResultEq.bind (T2Nat_ResultEq.refl _)
  intro q8
  apply T2Nat_ResultEq.bind (same _ _)
  rintro ⟨b9,r9⟩
  apply T2Nat_ResultEq.bind (T2Nat_ResultEq.refl _)
  intro q9
  apply T2Nat_ResultEq.bind (same _ _)
  rintro ⟨b10,r10⟩
  apply T2Nat_ResultEq.bind (T2Nat_ResultEq.refl _)
  intro q10
  apply T2Nat_ResultEq.bind (same _ _)
  rintro ⟨b11,r11⟩
  apply T2Nat_ResultEq.bind (T2Nat_ResultEq.refl _)
  intro q11
  apply T2Nat_ResultEq.bind (same _ _)
  rintro ⟨b12,r12⟩
  apply T2Nat_ResultEq.bind (T2Nat_ResultEq.refl _)
  intro q12
  apply T2Nat_ResultEq.bind (same _ _)
  rintro ⟨b13,r13⟩
  apply T2Nat_ResultEq.bind (T2Nat_ResultEq.refl _)
  intro q13
  apply T2Nat_ResultEq.bind (same _ _)
  rintro ⟨b14,r14⟩
  apply T2Nat_ResultEq.bind (T2Nat_ResultEq.refl _)
  intro q14
  apply T2Nat_ResultEq.bind (same _ _)
  rintro ⟨b15,r15⟩
  apply T2Nat_ResultEq.bind (T2Nat_ResultEq.refl _)
  intro q15
  apply T2Nat_ResultEq.bind (same _ _)
  rintro ⟨b16,r16⟩
  apply T2Nat_ResultEq.bind (T2Nat_ResultEq.refl _)
  intro q16
  apply T2Nat_ResultEq.bind (same _ _)
  rintro ⟨b17,r17⟩
  apply T2Nat_ResultEq.bind (T2Nat_ResultEq.refl _)
  intro q17
  apply T2Nat_ResultEq.bind (same _ _)
  rintro ⟨b18,r18⟩
  apply T2Nat_ResultEq.bind (T2Nat_ResultEq.refl _)
  intro q18
  apply T2Nat_ResultEq.bind (same _ _)
  rintro ⟨b19,r19⟩
  apply T2Nat_ResultEq.bind (T2Nat_ResultEq.refl _)
  intro q19
  apply T2Nat_ResultEq.bind (same _ _)
  rintro ⟨b20,r20⟩
  apply T2Nat_ResultEq.bind (T2Nat_ResultEq.refl _)
  intro q20
  apply T2Nat_ResultEq.bind (same _ _)
  rintro ⟨b21,r21⟩
  apply T2Nat_ResultEq.bind (T2Nat_ResultEq.refl _)
  intro q21
  exact T2Nat_ResultEq.refl _

#print axioms congr
end AspisR1.T2Nat_QueryReads
end
