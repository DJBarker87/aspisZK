import R1Z.PV_RDB2E_FallbackBlockTotal
import R1Z.PV_RDB2D_SHAModel
namespace R1Z.PV_RDB2F_ShaNi
open Aeneas Aeneas.Std Result PV_CBL_FallbackBlock
set_option autoImplicit false
abbrev Vec := Array U32 4#usize
abbrev State := Array U32 8#usize
abbrev Block := Array U8 64#usize
abbrev Words := Array U32 16#usize
/-- High-first lane encoding. shuffleRound is exactly shuffle(0x0E) then rnds2;
its unused upper lanes need not equal software swap's upper lanes. -/
structure Intrinsics where
  add : Vec → Vec → Result Vec
  round : Vec → Vec → Vec → Result Vec
  shuffleRound : Vec → Vec → Vec → Result Vec
  msg1 : Vec → Vec → Result Vec
  align4 : Vec → Vec → Result Vec
  msg2 : Vec → Vec → Result Vec
  pack : State → Result State
  load : Block → Result Words
  unpack : State → Result State

def referenceShuffleRound (a b t : Vec) : Result Vec := do
  let shuffled ← sha_fallback_reference.sha256swap t
  sha_fallback_reference.sha256_digest_round_x2 a b shuffled

/-- ONE explicit conditional instruction-semantics hypothesis, pending owner
item 3. This is neither a trust-list field nor a proved native instruction law.
pack/unpack include the listed loadu/shuffle/align/blend/store lane conversions;
load is loadu plus byte shuffle MASK. All equations concern local instruction
groups, never the desired digest/finalizer conclusion. -/
structure SHA_NI_IntrinsicsSemantics (intr : Intrinsics) : Prop where
  add : intr.add=sha_fallback_reference.add
  round : intr.round=sha_fallback_reference.sha256_digest_round_x2
  shuffleRound : intr.shuffleRound=referenceShuffleRound
  msg1 : intr.msg1=sha_fallback_reference.sha256msg1
  align4 : intr.align4=sha_fallback_reference.sha256load
  msg2 : intr.msg2=sha_fallback_reference.sha256msg2
  pack : ∀ s, intr.pack s=ok s
  load : intr.load=PV_CBL_ShaBytes.sha_load64
  unpack : ∀ s, intr.unpack s=ok s

def schedule (intr : Intrinsics) (v0 v1 v2 v3 : Vec) : Result Vec := do
  let t1 ← intr.msg1 v0 v1
  let t2 ← intr.align4 v2 v3
  let t3 ← intr.add t1 t2
  intr.msg2 t3 v3

theorem schedule_semantics (intr : Intrinsics) (h : SHA_NI_IntrinsicsSemantics intr) :
    schedule intr=sha_fallback_reference.schedule := by
  funext v0 v1 v2 v3
  simp only [schedule,sha_fallback_reference.schedule,h.msg1,h.align4,h.add,h.msg2]

def wordBlock (intr : Intrinsics)
  (state : Array Std.U32 8#usize) (block : Array Std.U32 16#usize) :
  Result (Array Std.U32 8#usize)
  := do
  let i ← Array.index_usize state 0#usize
  let i1 ← Array.index_usize state 1#usize
  let i2 ← Array.index_usize state 4#usize
  let i3 ← Array.index_usize state 5#usize
  let i4 ← Array.index_usize state 2#usize
  let i5 ← Array.index_usize state 3#usize
  let i6 ← Array.index_usize state 6#usize
  let i7 ← Array.index_usize state 7#usize
  let i8 ← Array.index_usize block 3#usize
  let i9 ← Array.index_usize block 2#usize
  let i10 ← Array.index_usize block 1#usize
  let i11 ← Array.index_usize block 0#usize
  let i12 ← Array.index_usize block 7#usize
  let i13 ← Array.index_usize block 6#usize
  let i14 ← Array.index_usize block 5#usize
  let i15 ← Array.index_usize block 4#usize
  let i16 ← Array.index_usize block 11#usize
  let i17 ← Array.index_usize block 10#usize
  let i18 ← Array.index_usize block 9#usize
  let i19 ← Array.index_usize block 8#usize
  let i20 ← Array.index_usize block 15#usize
  let i21 ← Array.index_usize block 14#usize
  let i22 ← Array.index_usize block 13#usize
  let i23 ← Array.index_usize block 12#usize
  let a ← sha_fallback_consts.K32X4
  let a1 ← Array.index_usize a 0#usize
  let t1 ←
    intr.add (Array.make 4#usize [ i8, i9, i10, i11 ]) a1
  let cdgh ←
    intr.round
      (Array.make 4#usize [ i4, i5, i6, i7 ])
      (Array.make 4#usize [ i, i1, i2, i3 ]) t1
  let abef ←
    intr.shuffleRound
      (Array.make 4#usize [ i, i1, i2, i3 ]) cdgh t1
  let a2 ← Array.index_usize a 1#usize
  let t11 ←
    intr.add (Array.make 4#usize [ i12, i13, i14, i15 ]) a2
  let cdgh1 ← intr.round cdgh abef t11
  let abef1 ← intr.shuffleRound abef cdgh1 t11
  let a3 ← Array.index_usize a 2#usize
  let t12 ←
    intr.add (Array.make 4#usize [ i16, i17, i18, i19 ]) a3
  let cdgh2 ← intr.round cdgh1 abef1 t12
  let abef2 ← intr.shuffleRound abef1 cdgh2 t12
  let a4 ← Array.index_usize a 3#usize
  let t13 ←
    intr.add (Array.make 4#usize [ i20, i21, i22, i23 ]) a4
  let cdgh3 ← intr.round cdgh2 abef2 t13
  let abef3 ← intr.shuffleRound abef2 cdgh3 t13
  let w4 ←
    schedule intr (Array.make 4#usize [ i8, i9, i10, i11 ])
      (Array.make 4#usize [ i12, i13, i14, i15 ])
      (Array.make 4#usize [ i16, i17, i18, i19 ])
      (Array.make 4#usize [ i20, i21, i22, i23 ])
  let a5 ← Array.index_usize a 4#usize
  let t14 ← intr.add w4 a5
  let cdgh4 ← intr.round cdgh3 abef3 t14
  let abef4 ← intr.shuffleRound abef3 cdgh4 t14
  let w0 ←
    schedule intr (Array.make 4#usize [ i12, i13, i14, i15 ])
      (Array.make 4#usize [ i16, i17, i18, i19 ])
      (Array.make 4#usize [ i20, i21, i22, i23 ]) w4
  let a6 ← Array.index_usize a 5#usize
  let t15 ← intr.add w0 a6
  let cdgh5 ← intr.round cdgh4 abef4 t15
  let abef5 ← intr.shuffleRound abef4 cdgh5 t15
  let w1 ←
    schedule intr (Array.make 4#usize [ i16, i17, i18, i19 ])
      (Array.make 4#usize [ i20, i21, i22, i23 ]) w4 w0
  let a7 ← Array.index_usize a 6#usize
  let t16 ← intr.add w1 a7
  let cdgh6 ← intr.round cdgh5 abef5 t16
  let abef6 ← intr.shuffleRound abef5 cdgh6 t16
  let w2 ←
    schedule intr (Array.make 4#usize [ i20, i21, i22, i23 ])
      w4 w0 w1
  let a8 ← Array.index_usize a 7#usize
  let t17 ← intr.add w2 a8
  let cdgh7 ← intr.round cdgh6 abef6 t17
  let abef7 ← intr.shuffleRound abef6 cdgh7 t17
  let w3 ← schedule intr w4 w0 w1 w2
  let a9 ← Array.index_usize a 8#usize
  let t18 ← intr.add w3 a9
  let cdgh8 ← intr.round cdgh7 abef7 t18
  let abef8 ← intr.shuffleRound abef7 cdgh8 t18
  let w41 ← schedule intr w0 w1 w2 w3
  let a10 ← Array.index_usize a 9#usize
  let t19 ← intr.add w41 a10
  let cdgh9 ← intr.round cdgh8 abef8 t19
  let abef9 ← intr.shuffleRound abef8 cdgh9 t19
  let w01 ← schedule intr w1 w2 w3 w41
  let a11 ← Array.index_usize a 10#usize
  let t110 ← intr.add w01 a11
  let cdgh10 ← intr.round cdgh9 abef9 t110
  let abef10 ←
    intr.shuffleRound abef9 cdgh10 t110
  let w11 ← schedule intr w2 w3 w41 w01
  let a12 ← Array.index_usize a 11#usize
  let t111 ← intr.add w11 a12
  let cdgh11 ←
    intr.round cdgh10 abef10 t111
  let abef11 ←
    intr.shuffleRound abef10 cdgh11 t111
  let w21 ← schedule intr w3 w41 w01 w11
  let a13 ← Array.index_usize a 12#usize
  let t112 ← intr.add w21 a13
  let cdgh12 ←
    intr.round cdgh11 abef11 t112
  let abef12 ←
    intr.shuffleRound abef11 cdgh12 t112
  let w31 ← schedule intr w41 w01 w11 w21
  let a14 ← Array.index_usize a 13#usize
  let t113 ← intr.add w31 a14
  let cdgh13 ←
    intr.round cdgh12 abef12 t113
  let abef13 ←
    intr.shuffleRound abef12 cdgh13 t113
  let w42 ← schedule intr w01 w11 w21 w31
  let a15 ← Array.index_usize a 14#usize
  let t114 ← intr.add w42 a15
  let cdgh14 ←
    intr.round cdgh13 abef13 t114
  let abef14 ←
    intr.shuffleRound abef13 cdgh14 t114
  let w02 ← schedule intr w11 w21 w31 w42
  let a16 ← Array.index_usize a 15#usize
  let t115 ← intr.add w02 a16
  let cdgh15 ←
    intr.round cdgh14 abef14 t115
  let abef15 ←
    intr.shuffleRound abef14 cdgh15 t115
  let a17 ← Array.index_usize abef15 0#usize
  let b ← Array.index_usize abef15 1#usize
  let e ← Array.index_usize abef15 2#usize
  let f ← Array.index_usize abef15 3#usize
  let c ← Array.index_usize cdgh15 0#usize
  let d ← Array.index_usize cdgh15 1#usize
  let g ← Array.index_usize cdgh15 2#usize
  let h ← Array.index_usize cdgh15 3#usize
  let i24 ← lift (core.num.U32.wrapping_add i a17)
  let state1 ← Array.update state 0#usize i24
  let i25 ← Array.index_usize state1 1#usize
  let i26 ← lift (core.num.U32.wrapping_add i25 b)
  let state2 ← Array.update state1 1#usize i26
  let i27 ← Array.index_usize state2 2#usize
  let i28 ← lift (core.num.U32.wrapping_add i27 c)
  let state3 ← Array.update state2 2#usize i28
  let i29 ← Array.index_usize state3 3#usize
  let i30 ← lift (core.num.U32.wrapping_add i29 d)
  let state4 ← Array.update state3 3#usize i30
  let i31 ← Array.index_usize state4 4#usize
  let i32 ← lift (core.num.U32.wrapping_add i31 e)
  let state5 ← Array.update state4 4#usize i32
  let i33 ← Array.index_usize state5 5#usize
  let i34 ← lift (core.num.U32.wrapping_add i33 f)
  let state6 ← Array.update state5 5#usize i34
  let i35 ← Array.index_usize state6 6#usize
  let i36 ← lift (core.num.U32.wrapping_add i35 g)
  let state7 ← Array.update state6 6#usize i36
  let i37 ← Array.index_usize state7 7#usize
  let i38 ← lift (core.num.U32.wrapping_add i37 h)
  Array.update state7 7#usize i38


theorem word_block_semantics (intr : Intrinsics) (h : SHA_NI_IntrinsicsSemantics intr)
    (state : State) (words : Words) :
    wordBlock intr state words=sha_fallback_reference.extracted_block state words := by
  simp only [wordBlock,sha_fallback_reference.extracted_block,
    sha_fallback_reference.sha256_digest_block_u32,h.add,h.round,h.shuffleRound,
    schedule_semantics intr h,referenceShuffleRound,bind_assoc_eq,bind_tc_ok]

#print axioms schedule_semantics
#print axioms word_block_semantics
end R1Z.PV_RDB2F_ShaNi
