import NIY_RawTransport
set_option autoImplicit false
noncomputable section
namespace NIY_QueryRead
open Aeneas Aeneas.Std Result

/-- Result associativity, including outer fail and divergence. -/
theorem assoc {A B C : Type} (m : Result A) (f : A → Result B) (g : B → Result C) :
 (do let y ← (do let x ← m;f x);g y)=(do let x ← m;let y ← f x;g y) := by
 cases m <;> rfl

def read22 {R : Type} (raw : R → Result (Array U8 4#usize × R)) (r12 : R) :
 Result (Array U32 22#usize × R) := do
 let (a5, r13) ← raw r12
 let i8 ← lift (core.num.U32.from_le_bytes a5)
 let (a6, r14) ← raw r13
 let i9 ← lift (core.num.U32.from_le_bytes a6)
 let (a7, r15) ← raw r14
 let i10 ← lift (core.num.U32.from_le_bytes a7)
 let (a8, r16) ← raw r15
 let i11 ← lift (core.num.U32.from_le_bytes a8)
 let (a9, r17) ← raw r16
 let i12 ← lift (core.num.U32.from_le_bytes a9)
 let (a10, r18) ←
   raw r17
 let i13 ← lift (core.num.U32.from_le_bytes a10)
 let (a11, r19) ←
   raw r18
 let i14 ← lift (core.num.U32.from_le_bytes a11)
 let (a12, r20) ←
   raw r19
 let i15 ← lift (core.num.U32.from_le_bytes a12)
 let (a13, r21) ←
   raw r20
 let i16 ← lift (core.num.U32.from_le_bytes a13)
 let (a14, r22) ←
   raw r21
 let i17 ← lift (core.num.U32.from_le_bytes a14)
 let (a15, r23) ←
   raw r22
 let i18 ← lift (core.num.U32.from_le_bytes a15)
 let (a16, r24) ←
   raw r23
 let i19 ← lift (core.num.U32.from_le_bytes a16)
 let (a17, r25) ←
   raw r24
 let i20 ← lift (core.num.U32.from_le_bytes a17)
 let (a18, r26) ←
   raw r25
 let i21 ← lift (core.num.U32.from_le_bytes a18)
 let (a19, r27) ←
   raw r26
 let i22 ← lift (core.num.U32.from_le_bytes a19)
 let (a20, r28) ←
   raw r27
 let i23 ← lift (core.num.U32.from_le_bytes a20)
 let (a21, r29) ←
   raw r28
 let i24 ← lift (core.num.U32.from_le_bytes a21)
 let (a22, r30) ←
   raw r29
 let i25 ← lift (core.num.U32.from_le_bytes a22)
 let (a23, r31) ←
   raw r30
 let i26 ← lift (core.num.U32.from_le_bytes a23)
 let (a24, r32) ←
   raw r31
 let i27 ← lift (core.num.U32.from_le_bytes a24)
 let (a25, r33) ←
   raw r32
 let i28 ← lift (core.num.U32.from_le_bytes a25)
 let (a26, r34) ←
   raw r33
 let i29 ← lift (core.num.U32.from_le_bytes a26)
 ok ((Array.make 22#usize [i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18, i19, i20, i21, i22, i23, i24, i25, i26, i27, i28, i29]),r34)

/-- Named ordered query continuation; the SAME final reader is passed to next. -/
theorem continuation {R A : Type} (raw : R → Result (Array U8 4#usize × R))
 (r12 : R) (next : Array U32 22#usize → R → Result A) :
 (do let (queries,out) ← read22 raw r12;next queries out)=(do
  let (a5, r13) ← raw r12
  let i8 ← lift (core.num.U32.from_le_bytes a5)
  let (a6, r14) ← raw r13
  let i9 ← lift (core.num.U32.from_le_bytes a6)
  let (a7, r15) ← raw r14
  let i10 ← lift (core.num.U32.from_le_bytes a7)
  let (a8, r16) ← raw r15
  let i11 ← lift (core.num.U32.from_le_bytes a8)
  let (a9, r17) ← raw r16
  let i12 ← lift (core.num.U32.from_le_bytes a9)
  let (a10, r18) ←
    raw r17
  let i13 ← lift (core.num.U32.from_le_bytes a10)
  let (a11, r19) ←
    raw r18
  let i14 ← lift (core.num.U32.from_le_bytes a11)
  let (a12, r20) ←
    raw r19
  let i15 ← lift (core.num.U32.from_le_bytes a12)
  let (a13, r21) ←
    raw r20
  let i16 ← lift (core.num.U32.from_le_bytes a13)
  let (a14, r22) ←
    raw r21
  let i17 ← lift (core.num.U32.from_le_bytes a14)
  let (a15, r23) ←
    raw r22
  let i18 ← lift (core.num.U32.from_le_bytes a15)
  let (a16, r24) ←
    raw r23
  let i19 ← lift (core.num.U32.from_le_bytes a16)
  let (a17, r25) ←
    raw r24
  let i20 ← lift (core.num.U32.from_le_bytes a17)
  let (a18, r26) ←
    raw r25
  let i21 ← lift (core.num.U32.from_le_bytes a18)
  let (a19, r27) ←
    raw r26
  let i22 ← lift (core.num.U32.from_le_bytes a19)
  let (a20, r28) ←
    raw r27
  let i23 ← lift (core.num.U32.from_le_bytes a20)
  let (a21, r29) ←
    raw r28
  let i24 ← lift (core.num.U32.from_le_bytes a21)
  let (a22, r30) ←
    raw r29
  let i25 ← lift (core.num.U32.from_le_bytes a22)
  let (a23, r31) ←
    raw r30
  let i26 ← lift (core.num.U32.from_le_bytes a23)
  let (a24, r32) ←
    raw r31
  let i27 ← lift (core.num.U32.from_le_bytes a24)
  let (a25, r33) ←
    raw r32
  let i28 ← lift (core.num.U32.from_le_bytes a25)
  let (a26, r34) ←
    raw r33
  let i29 ← lift (core.num.U32.from_le_bytes a26)
  next (Array.make 22#usize [i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18, i19, i20, i21, i22, i23, i24, i25, i26, i27, i28, i29]) r34) := by
 simp only [read22,assoc]

#print axioms assoc
#print axioms continuation
end NIY_QueryRead
