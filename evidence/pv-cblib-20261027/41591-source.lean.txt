import R1Z.PV_CBL_FallbackFourBind
import R1Z.PV_CBL_BlockBindExt
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_BlockValueFactored
set_option autoImplicit false
def block (state : Array U32 8#usize) (block : Array U32 16#usize) : Result (Array U32 8#usize) := do
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
  let a ← PV_CBL_FallbackBlock.sha_fallback_consts.K32X4
  let a1 ← Array.index_usize a 0#usize
  let (abef, cdgh) ← PV_CBL_FallbackFourModel.source (Array.make 4#usize [ i, i1, i2, i3 ]) (Array.make 4#usize [ i4, i5, i6, i7 ]) (Array.make 4#usize [ i8, i9, i10, i11 ]) a1
  let a2 ← Array.index_usize a 1#usize
  let (abef1, cdgh1) ← PV_CBL_FallbackFourModel.source abef cdgh (Array.make 4#usize [ i12, i13, i14, i15 ]) a2
  let a3 ← Array.index_usize a 2#usize
  let (abef2, cdgh2) ← PV_CBL_FallbackFourModel.source abef1 cdgh1 (Array.make 4#usize [ i16, i17, i18, i19 ]) a3
  let a4 ← Array.index_usize a 3#usize
  let (abef3, cdgh3) ← PV_CBL_FallbackFourModel.source abef2 cdgh2 (Array.make 4#usize [ i20, i21, i22, i23 ]) a4
  let w4 ←
    PV_CBL_FallbackBlock.sha_fallback_reference.schedule (Array.make 4#usize [ i8, i9, i10, i11 ])
      (Array.make 4#usize [ i12, i13, i14, i15 ])
      (Array.make 4#usize [ i16, i17, i18, i19 ])
      (Array.make 4#usize [ i20, i21, i22, i23 ])
  let a5 ← Array.index_usize a 4#usize
  let (abef4, cdgh4) ← PV_CBL_FallbackFourModel.source abef3 cdgh3 w4 a5
  let w0 ←
    PV_CBL_FallbackBlock.sha_fallback_reference.schedule (Array.make 4#usize [ i12, i13, i14, i15 ])
      (Array.make 4#usize [ i16, i17, i18, i19 ])
      (Array.make 4#usize [ i20, i21, i22, i23 ]) w4
  let a6 ← Array.index_usize a 5#usize
  let (abef5, cdgh5) ← PV_CBL_FallbackFourModel.source abef4 cdgh4 w0 a6
  let w1 ←
    PV_CBL_FallbackBlock.sha_fallback_reference.schedule (Array.make 4#usize [ i16, i17, i18, i19 ])
      (Array.make 4#usize [ i20, i21, i22, i23 ]) w4 w0
  let a7 ← Array.index_usize a 6#usize
  let (abef6, cdgh6) ← PV_CBL_FallbackFourModel.source abef5 cdgh5 w1 a7
  let w2 ←
    PV_CBL_FallbackBlock.sha_fallback_reference.schedule (Array.make 4#usize [ i20, i21, i22, i23 ])
      w4 w0 w1
  let a8 ← Array.index_usize a 7#usize
  let (abef7, cdgh7) ← PV_CBL_FallbackFourModel.source abef6 cdgh6 w2 a8
  let w3 ← PV_CBL_FallbackBlock.sha_fallback_reference.schedule w4 w0 w1 w2
  let a9 ← Array.index_usize a 8#usize
  let (abef8, cdgh8) ← PV_CBL_FallbackFourModel.source abef7 cdgh7 w3 a9
  let w41 ← PV_CBL_FallbackBlock.sha_fallback_reference.schedule w0 w1 w2 w3
  let a10 ← Array.index_usize a 9#usize
  let (abef9, cdgh9) ← PV_CBL_FallbackFourModel.source abef8 cdgh8 w41 a10
  let w01 ← PV_CBL_FallbackBlock.sha_fallback_reference.schedule w1 w2 w3 w41
  let a11 ← Array.index_usize a 10#usize
  let (abef10, cdgh10) ← PV_CBL_FallbackFourModel.source abef9 cdgh9 w01 a11
  let w11 ← PV_CBL_FallbackBlock.sha_fallback_reference.schedule w2 w3 w41 w01
  let a12 ← Array.index_usize a 11#usize
  let (abef11, cdgh11) ← PV_CBL_FallbackFourModel.source abef10 cdgh10 w11 a12
  let w21 ← PV_CBL_FallbackBlock.sha_fallback_reference.schedule w3 w41 w01 w11
  let a13 ← Array.index_usize a 12#usize
  let (abef12, cdgh12) ← PV_CBL_FallbackFourModel.source abef11 cdgh11 w21 a13
  let w31 ← PV_CBL_FallbackBlock.sha_fallback_reference.schedule w41 w01 w11 w21
  let a14 ← Array.index_usize a 13#usize
  let (abef13, cdgh13) ← PV_CBL_FallbackFourModel.source abef12 cdgh12 w31 a14
  let w42 ← PV_CBL_FallbackBlock.sha_fallback_reference.schedule w01 w11 w21 w31
  let a15 ← Array.index_usize a 14#usize
  let (abef14, cdgh14) ← PV_CBL_FallbackFourModel.source abef13 cdgh13 w42 a15
  let w02 ← PV_CBL_FallbackBlock.sha_fallback_reference.schedule w11 w21 w31 w42
  let a16 ← Array.index_usize a 15#usize
  let (abef15, cdgh15) ← PV_CBL_FallbackFourModel.source abef14 cdgh14 w02 a16
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
theorem source (state : Array U32 8#usize) (input : Array U32 16#usize) :
    PV_CBL_FallbackBlock.sha_fallback_reference.extracted_block state input = block state input := by
  apply PV_CBL_BlockBindExt.bind_ext
  intro i
  apply PV_CBL_BlockBindExt.bind_ext
  intro i1
  apply PV_CBL_BlockBindExt.bind_ext
  intro i2
  apply PV_CBL_BlockBindExt.bind_ext
  intro i3
  apply PV_CBL_BlockBindExt.bind_ext
  intro i4
  apply PV_CBL_BlockBindExt.bind_ext
  intro i5
  apply PV_CBL_BlockBindExt.bind_ext
  intro i6
  apply PV_CBL_BlockBindExt.bind_ext
  intro i7
  apply PV_CBL_BlockBindExt.bind_ext
  intro i8
  apply PV_CBL_BlockBindExt.bind_ext
  intro i9
  apply PV_CBL_BlockBindExt.bind_ext
  intro i10
  apply PV_CBL_BlockBindExt.bind_ext
  intro i11
  apply PV_CBL_BlockBindExt.bind_ext
  intro i12
  apply PV_CBL_BlockBindExt.bind_ext
  intro i13
  apply PV_CBL_BlockBindExt.bind_ext
  intro i14
  apply PV_CBL_BlockBindExt.bind_ext
  intro i15
  apply PV_CBL_BlockBindExt.bind_ext
  intro i16
  apply PV_CBL_BlockBindExt.bind_ext
  intro i17
  apply PV_CBL_BlockBindExt.bind_ext
  intro i18
  apply PV_CBL_BlockBindExt.bind_ext
  intro i19
  apply PV_CBL_BlockBindExt.bind_ext
  intro i20
  apply PV_CBL_BlockBindExt.bind_ext
  intro i21
  apply PV_CBL_BlockBindExt.bind_ext
  intro i22
  apply PV_CBL_BlockBindExt.bind_ext
  intro i23
  apply PV_CBL_BlockBindExt.bind_ext
  intro a
  apply PV_CBL_BlockBindExt.bind_ext
  intro a1
  conv_rhs => rw [PV_CBL_FallbackFourBind.expand]
  apply PV_CBL_BlockBindExt.bind_ext
  intro t1
  apply PV_CBL_BlockBindExt.bind_ext
  intro cdgh
  apply PV_CBL_BlockBindExt.bind_ext
  intro t2
  apply PV_CBL_BlockBindExt.bind_ext
  intro abef
  apply PV_CBL_BlockBindExt.bind_ext
  intro a2
  conv_rhs => rw [PV_CBL_FallbackFourBind.expand]
  apply PV_CBL_BlockBindExt.bind_ext
  intro t11
  apply PV_CBL_BlockBindExt.bind_ext
  intro cdgh1
  apply PV_CBL_BlockBindExt.bind_ext
  intro t21
  apply PV_CBL_BlockBindExt.bind_ext
  intro abef1
  apply PV_CBL_BlockBindExt.bind_ext
  intro a3
  conv_rhs => rw [PV_CBL_FallbackFourBind.expand]
  apply PV_CBL_BlockBindExt.bind_ext
  intro t12
  apply PV_CBL_BlockBindExt.bind_ext
  intro cdgh2
  apply PV_CBL_BlockBindExt.bind_ext
  intro t22
  apply PV_CBL_BlockBindExt.bind_ext
  intro abef2
  apply PV_CBL_BlockBindExt.bind_ext
  intro a4
  conv_rhs => rw [PV_CBL_FallbackFourBind.expand]
  apply PV_CBL_BlockBindExt.bind_ext
  intro t13
  apply PV_CBL_BlockBindExt.bind_ext
  intro cdgh3
  apply PV_CBL_BlockBindExt.bind_ext
  intro t23
  apply PV_CBL_BlockBindExt.bind_ext
  intro abef3
  apply PV_CBL_BlockBindExt.bind_ext
  intro w4
  apply PV_CBL_BlockBindExt.bind_ext
  intro a5
  conv_rhs => rw [PV_CBL_FallbackFourBind.expand]
  apply PV_CBL_BlockBindExt.bind_ext
  intro t14
  apply PV_CBL_BlockBindExt.bind_ext
  intro cdgh4
  apply PV_CBL_BlockBindExt.bind_ext
  intro t24
  apply PV_CBL_BlockBindExt.bind_ext
  intro abef4
  apply PV_CBL_BlockBindExt.bind_ext
  intro w0
  apply PV_CBL_BlockBindExt.bind_ext
  intro a6
  conv_rhs => rw [PV_CBL_FallbackFourBind.expand]
  apply PV_CBL_BlockBindExt.bind_ext
  intro t15
  apply PV_CBL_BlockBindExt.bind_ext
  intro cdgh5
  apply PV_CBL_BlockBindExt.bind_ext
  intro t25
  apply PV_CBL_BlockBindExt.bind_ext
  intro abef5
  apply PV_CBL_BlockBindExt.bind_ext
  intro w1
  apply PV_CBL_BlockBindExt.bind_ext
  intro a7
  conv_rhs => rw [PV_CBL_FallbackFourBind.expand]
  apply PV_CBL_BlockBindExt.bind_ext
  intro t16
  apply PV_CBL_BlockBindExt.bind_ext
  intro cdgh6
  apply PV_CBL_BlockBindExt.bind_ext
  intro t26
  apply PV_CBL_BlockBindExt.bind_ext
  intro abef6
  apply PV_CBL_BlockBindExt.bind_ext
  intro w2
  apply PV_CBL_BlockBindExt.bind_ext
  intro a8
  conv_rhs => rw [PV_CBL_FallbackFourBind.expand]
  apply PV_CBL_BlockBindExt.bind_ext
  intro t17
  apply PV_CBL_BlockBindExt.bind_ext
  intro cdgh7
  apply PV_CBL_BlockBindExt.bind_ext
  intro t27
  apply PV_CBL_BlockBindExt.bind_ext
  intro abef7
  apply PV_CBL_BlockBindExt.bind_ext
  intro w3
  apply PV_CBL_BlockBindExt.bind_ext
  intro a9
  conv_rhs => rw [PV_CBL_FallbackFourBind.expand]
  apply PV_CBL_BlockBindExt.bind_ext
  intro t18
  apply PV_CBL_BlockBindExt.bind_ext
  intro cdgh8
  apply PV_CBL_BlockBindExt.bind_ext
  intro t28
  apply PV_CBL_BlockBindExt.bind_ext
  intro abef8
  apply PV_CBL_BlockBindExt.bind_ext
  intro w41
  apply PV_CBL_BlockBindExt.bind_ext
  intro a10
  conv_rhs => rw [PV_CBL_FallbackFourBind.expand]
  apply PV_CBL_BlockBindExt.bind_ext
  intro t19
  apply PV_CBL_BlockBindExt.bind_ext
  intro cdgh9
  apply PV_CBL_BlockBindExt.bind_ext
  intro t29
  apply PV_CBL_BlockBindExt.bind_ext
  intro abef9
  apply PV_CBL_BlockBindExt.bind_ext
  intro w01
  apply PV_CBL_BlockBindExt.bind_ext
  intro a11
  conv_rhs => rw [PV_CBL_FallbackFourBind.expand]
  apply PV_CBL_BlockBindExt.bind_ext
  intro t110
  apply PV_CBL_BlockBindExt.bind_ext
  intro cdgh10
  apply PV_CBL_BlockBindExt.bind_ext
  intro t210
  apply PV_CBL_BlockBindExt.bind_ext
  intro abef10
  apply PV_CBL_BlockBindExt.bind_ext
  intro w11
  apply PV_CBL_BlockBindExt.bind_ext
  intro a12
  conv_rhs => rw [PV_CBL_FallbackFourBind.expand]
  apply PV_CBL_BlockBindExt.bind_ext
  intro t111
  apply PV_CBL_BlockBindExt.bind_ext
  intro cdgh11
  apply PV_CBL_BlockBindExt.bind_ext
  intro t211
  apply PV_CBL_BlockBindExt.bind_ext
  intro abef11
  apply PV_CBL_BlockBindExt.bind_ext
  intro w21
  apply PV_CBL_BlockBindExt.bind_ext
  intro a13
  conv_rhs => rw [PV_CBL_FallbackFourBind.expand]
  apply PV_CBL_BlockBindExt.bind_ext
  intro t112
  apply PV_CBL_BlockBindExt.bind_ext
  intro cdgh12
  apply PV_CBL_BlockBindExt.bind_ext
  intro t212
  apply PV_CBL_BlockBindExt.bind_ext
  intro abef12
  apply PV_CBL_BlockBindExt.bind_ext
  intro w31
  apply PV_CBL_BlockBindExt.bind_ext
  intro a14
  conv_rhs => rw [PV_CBL_FallbackFourBind.expand]
  apply PV_CBL_BlockBindExt.bind_ext
  intro t113
  apply PV_CBL_BlockBindExt.bind_ext
  intro cdgh13
  apply PV_CBL_BlockBindExt.bind_ext
  intro t213
  apply PV_CBL_BlockBindExt.bind_ext
  intro abef13
  apply PV_CBL_BlockBindExt.bind_ext
  intro w42
  apply PV_CBL_BlockBindExt.bind_ext
  intro a15
  conv_rhs => rw [PV_CBL_FallbackFourBind.expand]
  apply PV_CBL_BlockBindExt.bind_ext
  intro t114
  apply PV_CBL_BlockBindExt.bind_ext
  intro cdgh14
  apply PV_CBL_BlockBindExt.bind_ext
  intro t214
  apply PV_CBL_BlockBindExt.bind_ext
  intro abef14
  apply PV_CBL_BlockBindExt.bind_ext
  intro w02
  apply PV_CBL_BlockBindExt.bind_ext
  intro a16
  conv_rhs => rw [PV_CBL_FallbackFourBind.expand]
  apply PV_CBL_BlockBindExt.bind_ext
  intro t115
  apply PV_CBL_BlockBindExt.bind_ext
  intro cdgh15
  apply PV_CBL_BlockBindExt.bind_ext
  intro t215
  apply PV_CBL_BlockBindExt.bind_ext
  intro abef15
  apply PV_CBL_BlockBindExt.bind_ext
  intro a17
  apply PV_CBL_BlockBindExt.bind_ext
  intro b
  apply PV_CBL_BlockBindExt.bind_ext
  intro e
  apply PV_CBL_BlockBindExt.bind_ext
  intro f
  apply PV_CBL_BlockBindExt.bind_ext
  intro c
  apply PV_CBL_BlockBindExt.bind_ext
  intro d
  apply PV_CBL_BlockBindExt.bind_ext
  intro g
  apply PV_CBL_BlockBindExt.bind_ext
  intro h
  apply PV_CBL_BlockBindExt.bind_ext
  intro i24
  apply PV_CBL_BlockBindExt.bind_ext
  intro state1
  apply PV_CBL_BlockBindExt.bind_ext
  intro i25
  apply PV_CBL_BlockBindExt.bind_ext
  intro i26
  apply PV_CBL_BlockBindExt.bind_ext
  intro state2
  apply PV_CBL_BlockBindExt.bind_ext
  intro i27
  apply PV_CBL_BlockBindExt.bind_ext
  intro i28
  apply PV_CBL_BlockBindExt.bind_ext
  intro state3
  apply PV_CBL_BlockBindExt.bind_ext
  intro i29
  apply PV_CBL_BlockBindExt.bind_ext
  intro i30
  apply PV_CBL_BlockBindExt.bind_ext
  intro state4
  apply PV_CBL_BlockBindExt.bind_ext
  intro i31
  apply PV_CBL_BlockBindExt.bind_ext
  intro i32
  apply PV_CBL_BlockBindExt.bind_ext
  intro state5
  apply PV_CBL_BlockBindExt.bind_ext
  intro i33
  apply PV_CBL_BlockBindExt.bind_ext
  intro i34
  apply PV_CBL_BlockBindExt.bind_ext
  intro state6
  apply PV_CBL_BlockBindExt.bind_ext
  intro i35
  apply PV_CBL_BlockBindExt.bind_ext
  intro i36
  apply PV_CBL_BlockBindExt.bind_ext
  intro state7
  apply PV_CBL_BlockBindExt.bind_ext
  intro i37
  apply PV_CBL_BlockBindExt.bind_ext
  intro i38
  rfl
#print axioms source
end R1Z.PV_CBL_BlockValueFactored
