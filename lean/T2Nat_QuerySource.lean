import T2Nat_AfterQueries
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_QuerySource
open Aeneas Aeneas.Std Result AspisR1Stage2
def source (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (i4 : U8) (end1 : Usize) (state a3 a4 : Array U8 32#usize)
    (val val1 val2 val3 : T2Nat_ReaderSuffix.E) (val4 : T2Nat_ReaderSuffix.K)
    (r : verifier.Reader) :
    Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
  let (a5, r13) ← ops.raw 4#usize r
  let i8 ← lift (core.num.U32.from_le_bytes a5)
  let (a6, r14) ← ops.raw 4#usize r13
  let i9 ← lift (core.num.U32.from_le_bytes a6)
  let (a7, r15) ← ops.raw 4#usize r14
  let i10 ← lift (core.num.U32.from_le_bytes a7)
  let (a8, r16) ← ops.raw 4#usize r15
  let i11 ← lift (core.num.U32.from_le_bytes a8)
  let (a9, r17) ← ops.raw 4#usize r16
  let i12 ← lift (core.num.U32.from_le_bytes a9)
  let (a10, r18) ←
    ops.raw 4#usize r17
  let i13 ← lift (core.num.U32.from_le_bytes a10)
  let (a11, r19) ←
    ops.raw 4#usize r18
  let i14 ← lift (core.num.U32.from_le_bytes a11)
  let (a12, r20) ←
    ops.raw 4#usize r19
  let i15 ← lift (core.num.U32.from_le_bytes a12)
  let (a13, r21) ←
    ops.raw 4#usize r20
  let i16 ← lift (core.num.U32.from_le_bytes a13)
  let (a14, r22) ←
    ops.raw 4#usize r21
  let i17 ← lift (core.num.U32.from_le_bytes a14)
  let (a15, r23) ←
    ops.raw 4#usize r22
  let i18 ← lift (core.num.U32.from_le_bytes a15)
  let (a16, r24) ←
    ops.raw 4#usize r23
  let i19 ← lift (core.num.U32.from_le_bytes a16)
  let (a17, r25) ←
    ops.raw 4#usize r24
  let i20 ← lift (core.num.U32.from_le_bytes a17)
  let (a18, r26) ←
    ops.raw 4#usize r25
  let i21 ← lift (core.num.U32.from_le_bytes a18)
  let (a19, r27) ←
    ops.raw 4#usize r26
  let i22 ← lift (core.num.U32.from_le_bytes a19)
  let (a20, r28) ←
    ops.raw 4#usize r27
  let i23 ← lift (core.num.U32.from_le_bytes a20)
  let (a21, r29) ←
    ops.raw 4#usize r28
  let i24 ← lift (core.num.U32.from_le_bytes a21)
  let (a22, r30) ←
    ops.raw 4#usize r29
  let i25 ← lift (core.num.U32.from_le_bytes a22)
  let (a23, r31) ←
    ops.raw 4#usize r30
  let i26 ← lift (core.num.U32.from_le_bytes a23)
  let (a24, r32) ←
    ops.raw 4#usize r31
  let i27 ← lift (core.num.U32.from_le_bytes a24)
  let (a25, r33) ←
    ops.raw 4#usize r32
  let i28 ← lift (core.num.U32.from_le_bytes a25)
  let (a26, r34) ←
    ops.raw 4#usize r33
  let i29 ← lift (core.num.U32.from_le_bytes a26)
  T2Nat_AfterQueries.source ops bytes v i4 end1 state a3 a4 val val1 val2 val3 val4
    (Array.make 22#usize [ i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18, i19, i20, i21, i22, i23, i24, i25, i26, i27, i28, i29 ]) r34

def normalized (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (i4 : U8) (end1 : Usize) (state a3 a4 : Array U8 32#usize)
    (val val1 val2 val3 : T2Nat_ReaderSuffix.E) (val4 : T2Nat_ReaderSuffix.K)
    (r : verifier.Reader) :
    Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
  let (queries,out) ← T2Nat_QueryReads.queries ops.raw r
  T2Nat_AfterQueries.normalized ops bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 queries out

theorem normalize (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (i4 : U8) (end1 : Usize) (state a3 a4 : Array U8 32#usize)
    (val val1 val2 val3 : T2Nat_ReaderSuffix.E) (val4 : T2Nat_ReaderSuffix.K)
    (r : verifier.Reader) :
    source ops bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 r =
      normalized ops bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 r := by
  simp only [source,normalized,T2Nat_QueryReads.queries,T2Nat_AfterQueries.normalize,
    bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry]
  repeat
    first
    | rfl
    | (apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro x hx; try rcases x with ⟨a,b⟩; try simp only [Aeneas.Std.uncurry])

#print axioms normalize
end AspisR1.T2Nat_QuerySource
end
