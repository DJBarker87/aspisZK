import R1Z.PV_RDB2E_FallbackHelpersTotal
import R1Z.PV_RDB2E_FallbackConstants

section
-- Unchanged source component R1Z.PV_CBL_FallbackBlockTotal
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackBlockTotal
open PV_CBL_FallbackTotal
set_option autoImplicit false
theorem constants : Total PV_CBL_FallbackBlock.sha_fallback_consts.K32X4 :=
  ⟨_,PV_CBL_FallbackConstantSource.source⟩
/-- Linear symbolic totality proof; no helper or arithmetic state normalization. -/
theorem total (state : Array U32 8#usize) (input : Array U32 16#usize) :
    Total (PV_CBL_FallbackBlock.sha_fallback_reference.extracted_block state input) := by
  unfold PV_CBL_FallbackBlock.sha_fallback_reference.extracted_block
    PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_block_u32
  refine PV_CBL_FallbackTotal.bind (Array.index_usize state 0#usize) _ (PV_CBL_FallbackTotal.read state 0#usize (by decide)) ?_
  intro i
  refine PV_CBL_FallbackTotal.bind (Array.index_usize state 1#usize) _ (PV_CBL_FallbackTotal.read state 1#usize (by decide)) ?_
  intro i1
  refine PV_CBL_FallbackTotal.bind (Array.index_usize state 4#usize) _ (PV_CBL_FallbackTotal.read state 4#usize (by decide)) ?_
  intro i2
  refine PV_CBL_FallbackTotal.bind (Array.index_usize state 5#usize) _ (PV_CBL_FallbackTotal.read state 5#usize (by decide)) ?_
  intro i3
  refine PV_CBL_FallbackTotal.bind (Array.index_usize state 2#usize) _ (PV_CBL_FallbackTotal.read state 2#usize (by decide)) ?_
  intro i4
  refine PV_CBL_FallbackTotal.bind (Array.index_usize state 3#usize) _ (PV_CBL_FallbackTotal.read state 3#usize (by decide)) ?_
  intro i5
  refine PV_CBL_FallbackTotal.bind (Array.index_usize state 6#usize) _ (PV_CBL_FallbackTotal.read state 6#usize (by decide)) ?_
  intro i6
  refine PV_CBL_FallbackTotal.bind (Array.index_usize state 7#usize) _ (PV_CBL_FallbackTotal.read state 7#usize (by decide)) ?_
  intro i7
  refine PV_CBL_FallbackTotal.bind (Array.index_usize input 3#usize) _ (PV_CBL_FallbackTotal.read input 3#usize (by decide)) ?_
  intro i8
  refine PV_CBL_FallbackTotal.bind (Array.index_usize input 2#usize) _ (PV_CBL_FallbackTotal.read input 2#usize (by decide)) ?_
  intro i9
  refine PV_CBL_FallbackTotal.bind (Array.index_usize input 1#usize) _ (PV_CBL_FallbackTotal.read input 1#usize (by decide)) ?_
  intro i10
  refine PV_CBL_FallbackTotal.bind (Array.index_usize input 0#usize) _ (PV_CBL_FallbackTotal.read input 0#usize (by decide)) ?_
  intro i11
  refine PV_CBL_FallbackTotal.bind (Array.index_usize input 7#usize) _ (PV_CBL_FallbackTotal.read input 7#usize (by decide)) ?_
  intro i12
  refine PV_CBL_FallbackTotal.bind (Array.index_usize input 6#usize) _ (PV_CBL_FallbackTotal.read input 6#usize (by decide)) ?_
  intro i13
  refine PV_CBL_FallbackTotal.bind (Array.index_usize input 5#usize) _ (PV_CBL_FallbackTotal.read input 5#usize (by decide)) ?_
  intro i14
  refine PV_CBL_FallbackTotal.bind (Array.index_usize input 4#usize) _ (PV_CBL_FallbackTotal.read input 4#usize (by decide)) ?_
  intro i15
  refine PV_CBL_FallbackTotal.bind (Array.index_usize input 11#usize) _ (PV_CBL_FallbackTotal.read input 11#usize (by decide)) ?_
  intro i16
  refine PV_CBL_FallbackTotal.bind (Array.index_usize input 10#usize) _ (PV_CBL_FallbackTotal.read input 10#usize (by decide)) ?_
  intro i17
  refine PV_CBL_FallbackTotal.bind (Array.index_usize input 9#usize) _ (PV_CBL_FallbackTotal.read input 9#usize (by decide)) ?_
  intro i18
  refine PV_CBL_FallbackTotal.bind (Array.index_usize input 8#usize) _ (PV_CBL_FallbackTotal.read input 8#usize (by decide)) ?_
  intro i19
  refine PV_CBL_FallbackTotal.bind (Array.index_usize input 15#usize) _ (PV_CBL_FallbackTotal.read input 15#usize (by decide)) ?_
  intro i20
  refine PV_CBL_FallbackTotal.bind (Array.index_usize input 14#usize) _ (PV_CBL_FallbackTotal.read input 14#usize (by decide)) ?_
  intro i21
  refine PV_CBL_FallbackTotal.bind (Array.index_usize input 13#usize) _ (PV_CBL_FallbackTotal.read input 13#usize (by decide)) ?_
  intro i22
  refine PV_CBL_FallbackTotal.bind (Array.index_usize input 12#usize) _ (PV_CBL_FallbackTotal.read input 12#usize (by decide)) ?_
  intro i23
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_consts.K32X4) _ (constants) ?_
  intro a
  refine PV_CBL_FallbackTotal.bind (Array.index_usize a 0#usize) _ (PV_CBL_FallbackTotal.read a 0#usize (by decide)) ?_
  intro a1
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.add (Array.make 4#usize [ i8, i9, i10, i11 ]) a1) _ (PV_CBL_FallbackHelpersTotal.add (Array.make 4#usize [ i8, i9, i10, i11 ]) a1) ?_
  intro t1
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 (Array.make 4#usize [ i4, i5, i6, i7 ]) (Array.make 4#usize [ i, i1, i2, i3 ]) t1) _ (PV_CBL_FallbackHelpersTotal.round (Array.make 4#usize [ i4, i5, i6, i7 ]) (Array.make 4#usize [ i, i1, i2, i3 ]) t1) ?_
  intro cdgh
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256swap t1) _ (PV_CBL_FallbackHelpersTotal.swap t1) ?_
  intro t2
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 (Array.make 4#usize [ i, i1, i2, i3 ]) cdgh t2) _ (PV_CBL_FallbackHelpersTotal.round (Array.make 4#usize [ i, i1, i2, i3 ]) cdgh t2) ?_
  intro abef
  refine PV_CBL_FallbackTotal.bind (Array.index_usize a 1#usize) _ (PV_CBL_FallbackTotal.read a 1#usize (by decide)) ?_
  intro a2
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.add (Array.make 4#usize [ i12, i13, i14, i15 ]) a2) _ (PV_CBL_FallbackHelpersTotal.add (Array.make 4#usize [ i12, i13, i14, i15 ]) a2) ?_
  intro t11
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 cdgh abef t11) _ (PV_CBL_FallbackHelpersTotal.round cdgh abef t11) ?_
  intro cdgh1
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256swap t11) _ (PV_CBL_FallbackHelpersTotal.swap t11) ?_
  intro t21
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 abef cdgh1 t21) _ (PV_CBL_FallbackHelpersTotal.round abef cdgh1 t21) ?_
  intro abef1
  refine PV_CBL_FallbackTotal.bind (Array.index_usize a 2#usize) _ (PV_CBL_FallbackTotal.read a 2#usize (by decide)) ?_
  intro a3
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.add (Array.make 4#usize [ i16, i17, i18, i19 ]) a3) _ (PV_CBL_FallbackHelpersTotal.add (Array.make 4#usize [ i16, i17, i18, i19 ]) a3) ?_
  intro t12
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 cdgh1 abef1 t12) _ (PV_CBL_FallbackHelpersTotal.round cdgh1 abef1 t12) ?_
  intro cdgh2
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256swap t12) _ (PV_CBL_FallbackHelpersTotal.swap t12) ?_
  intro t22
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 abef1 cdgh2 t22) _ (PV_CBL_FallbackHelpersTotal.round abef1 cdgh2 t22) ?_
  intro abef2
  refine PV_CBL_FallbackTotal.bind (Array.index_usize a 3#usize) _ (PV_CBL_FallbackTotal.read a 3#usize (by decide)) ?_
  intro a4
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.add (Array.make 4#usize [ i20, i21, i22, i23 ]) a4) _ (PV_CBL_FallbackHelpersTotal.add (Array.make 4#usize [ i20, i21, i22, i23 ]) a4) ?_
  intro t13
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 cdgh2 abef2 t13) _ (PV_CBL_FallbackHelpersTotal.round cdgh2 abef2 t13) ?_
  intro cdgh3
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256swap t13) _ (PV_CBL_FallbackHelpersTotal.swap t13) ?_
  intro t23
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 abef2 cdgh3 t23) _ (PV_CBL_FallbackHelpersTotal.round abef2 cdgh3 t23) ?_
  intro abef3
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.schedule (Array.make 4#usize [ i8, i9, i10, i11 ]) (Array.make 4#usize [ i12, i13, i14, i15 ]) (Array.make 4#usize [ i16, i17, i18, i19 ]) (Array.make 4#usize [ i20, i21, i22, i23 ])) _ (PV_CBL_FallbackHelpersTotal.schedule (Array.make 4#usize [ i8, i9, i10, i11 ]) (Array.make 4#usize [ i12, i13, i14, i15 ]) (Array.make 4#usize [ i16, i17, i18, i19 ]) (Array.make 4#usize [ i20, i21, i22, i23 ])) ?_
  intro w4
  refine PV_CBL_FallbackTotal.bind (Array.index_usize a 4#usize) _ (PV_CBL_FallbackTotal.read a 4#usize (by decide)) ?_
  intro a5
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.add w4 a5) _ (PV_CBL_FallbackHelpersTotal.add w4 a5) ?_
  intro t14
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 cdgh3 abef3 t14) _ (PV_CBL_FallbackHelpersTotal.round cdgh3 abef3 t14) ?_
  intro cdgh4
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256swap t14) _ (PV_CBL_FallbackHelpersTotal.swap t14) ?_
  intro t24
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 abef3 cdgh4 t24) _ (PV_CBL_FallbackHelpersTotal.round abef3 cdgh4 t24) ?_
  intro abef4
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.schedule (Array.make 4#usize [ i12, i13, i14, i15 ]) (Array.make 4#usize [ i16, i17, i18, i19 ]) (Array.make 4#usize [ i20, i21, i22, i23 ]) w4) _ (PV_CBL_FallbackHelpersTotal.schedule (Array.make 4#usize [ i12, i13, i14, i15 ]) (Array.make 4#usize [ i16, i17, i18, i19 ]) (Array.make 4#usize [ i20, i21, i22, i23 ]) w4) ?_
  intro w0
  refine PV_CBL_FallbackTotal.bind (Array.index_usize a 5#usize) _ (PV_CBL_FallbackTotal.read a 5#usize (by decide)) ?_
  intro a6
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.add w0 a6) _ (PV_CBL_FallbackHelpersTotal.add w0 a6) ?_
  intro t15
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 cdgh4 abef4 t15) _ (PV_CBL_FallbackHelpersTotal.round cdgh4 abef4 t15) ?_
  intro cdgh5
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256swap t15) _ (PV_CBL_FallbackHelpersTotal.swap t15) ?_
  intro t25
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 abef4 cdgh5 t25) _ (PV_CBL_FallbackHelpersTotal.round abef4 cdgh5 t25) ?_
  intro abef5
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.schedule (Array.make 4#usize [ i16, i17, i18, i19 ]) (Array.make 4#usize [ i20, i21, i22, i23 ]) w4 w0) _ (PV_CBL_FallbackHelpersTotal.schedule (Array.make 4#usize [ i16, i17, i18, i19 ]) (Array.make 4#usize [ i20, i21, i22, i23 ]) w4 w0) ?_
  intro w1
  refine PV_CBL_FallbackTotal.bind (Array.index_usize a 6#usize) _ (PV_CBL_FallbackTotal.read a 6#usize (by decide)) ?_
  intro a7
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.add w1 a7) _ (PV_CBL_FallbackHelpersTotal.add w1 a7) ?_
  intro t16
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 cdgh5 abef5 t16) _ (PV_CBL_FallbackHelpersTotal.round cdgh5 abef5 t16) ?_
  intro cdgh6
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256swap t16) _ (PV_CBL_FallbackHelpersTotal.swap t16) ?_
  intro t26
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 abef5 cdgh6 t26) _ (PV_CBL_FallbackHelpersTotal.round abef5 cdgh6 t26) ?_
  intro abef6
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.schedule (Array.make 4#usize [ i20, i21, i22, i23 ]) w4 w0 w1) _ (PV_CBL_FallbackHelpersTotal.schedule (Array.make 4#usize [ i20, i21, i22, i23 ]) w4 w0 w1) ?_
  intro w2
  refine PV_CBL_FallbackTotal.bind (Array.index_usize a 7#usize) _ (PV_CBL_FallbackTotal.read a 7#usize (by decide)) ?_
  intro a8
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.add w2 a8) _ (PV_CBL_FallbackHelpersTotal.add w2 a8) ?_
  intro t17
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 cdgh6 abef6 t17) _ (PV_CBL_FallbackHelpersTotal.round cdgh6 abef6 t17) ?_
  intro cdgh7
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256swap t17) _ (PV_CBL_FallbackHelpersTotal.swap t17) ?_
  intro t27
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 abef6 cdgh7 t27) _ (PV_CBL_FallbackHelpersTotal.round abef6 cdgh7 t27) ?_
  intro abef7
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.schedule w4 w0 w1 w2) _ (PV_CBL_FallbackHelpersTotal.schedule w4 w0 w1 w2) ?_
  intro w3
  refine PV_CBL_FallbackTotal.bind (Array.index_usize a 8#usize) _ (PV_CBL_FallbackTotal.read a 8#usize (by decide)) ?_
  intro a9
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.add w3 a9) _ (PV_CBL_FallbackHelpersTotal.add w3 a9) ?_
  intro t18
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 cdgh7 abef7 t18) _ (PV_CBL_FallbackHelpersTotal.round cdgh7 abef7 t18) ?_
  intro cdgh8
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256swap t18) _ (PV_CBL_FallbackHelpersTotal.swap t18) ?_
  intro t28
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 abef7 cdgh8 t28) _ (PV_CBL_FallbackHelpersTotal.round abef7 cdgh8 t28) ?_
  intro abef8
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.schedule w0 w1 w2 w3) _ (PV_CBL_FallbackHelpersTotal.schedule w0 w1 w2 w3) ?_
  intro w41
  refine PV_CBL_FallbackTotal.bind (Array.index_usize a 9#usize) _ (PV_CBL_FallbackTotal.read a 9#usize (by decide)) ?_
  intro a10
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.add w41 a10) _ (PV_CBL_FallbackHelpersTotal.add w41 a10) ?_
  intro t19
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 cdgh8 abef8 t19) _ (PV_CBL_FallbackHelpersTotal.round cdgh8 abef8 t19) ?_
  intro cdgh9
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256swap t19) _ (PV_CBL_FallbackHelpersTotal.swap t19) ?_
  intro t29
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 abef8 cdgh9 t29) _ (PV_CBL_FallbackHelpersTotal.round abef8 cdgh9 t29) ?_
  intro abef9
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.schedule w1 w2 w3 w41) _ (PV_CBL_FallbackHelpersTotal.schedule w1 w2 w3 w41) ?_
  intro w01
  refine PV_CBL_FallbackTotal.bind (Array.index_usize a 10#usize) _ (PV_CBL_FallbackTotal.read a 10#usize (by decide)) ?_
  intro a11
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.add w01 a11) _ (PV_CBL_FallbackHelpersTotal.add w01 a11) ?_
  intro t110
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 cdgh9 abef9 t110) _ (PV_CBL_FallbackHelpersTotal.round cdgh9 abef9 t110) ?_
  intro cdgh10
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256swap t110) _ (PV_CBL_FallbackHelpersTotal.swap t110) ?_
  intro t210
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 abef9 cdgh10 t210) _ (PV_CBL_FallbackHelpersTotal.round abef9 cdgh10 t210) ?_
  intro abef10
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.schedule w2 w3 w41 w01) _ (PV_CBL_FallbackHelpersTotal.schedule w2 w3 w41 w01) ?_
  intro w11
  refine PV_CBL_FallbackTotal.bind (Array.index_usize a 11#usize) _ (PV_CBL_FallbackTotal.read a 11#usize (by decide)) ?_
  intro a12
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.add w11 a12) _ (PV_CBL_FallbackHelpersTotal.add w11 a12) ?_
  intro t111
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 cdgh10 abef10 t111) _ (PV_CBL_FallbackHelpersTotal.round cdgh10 abef10 t111) ?_
  intro cdgh11
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256swap t111) _ (PV_CBL_FallbackHelpersTotal.swap t111) ?_
  intro t211
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 abef10 cdgh11 t211) _ (PV_CBL_FallbackHelpersTotal.round abef10 cdgh11 t211) ?_
  intro abef11
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.schedule w3 w41 w01 w11) _ (PV_CBL_FallbackHelpersTotal.schedule w3 w41 w01 w11) ?_
  intro w21
  refine PV_CBL_FallbackTotal.bind (Array.index_usize a 12#usize) _ (PV_CBL_FallbackTotal.read a 12#usize (by decide)) ?_
  intro a13
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.add w21 a13) _ (PV_CBL_FallbackHelpersTotal.add w21 a13) ?_
  intro t112
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 cdgh11 abef11 t112) _ (PV_CBL_FallbackHelpersTotal.round cdgh11 abef11 t112) ?_
  intro cdgh12
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256swap t112) _ (PV_CBL_FallbackHelpersTotal.swap t112) ?_
  intro t212
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 abef11 cdgh12 t212) _ (PV_CBL_FallbackHelpersTotal.round abef11 cdgh12 t212) ?_
  intro abef12
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.schedule w41 w01 w11 w21) _ (PV_CBL_FallbackHelpersTotal.schedule w41 w01 w11 w21) ?_
  intro w31
  refine PV_CBL_FallbackTotal.bind (Array.index_usize a 13#usize) _ (PV_CBL_FallbackTotal.read a 13#usize (by decide)) ?_
  intro a14
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.add w31 a14) _ (PV_CBL_FallbackHelpersTotal.add w31 a14) ?_
  intro t113
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 cdgh12 abef12 t113) _ (PV_CBL_FallbackHelpersTotal.round cdgh12 abef12 t113) ?_
  intro cdgh13
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256swap t113) _ (PV_CBL_FallbackHelpersTotal.swap t113) ?_
  intro t213
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 abef12 cdgh13 t213) _ (PV_CBL_FallbackHelpersTotal.round abef12 cdgh13 t213) ?_
  intro abef13
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.schedule w01 w11 w21 w31) _ (PV_CBL_FallbackHelpersTotal.schedule w01 w11 w21 w31) ?_
  intro w42
  refine PV_CBL_FallbackTotal.bind (Array.index_usize a 14#usize) _ (PV_CBL_FallbackTotal.read a 14#usize (by decide)) ?_
  intro a15
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.add w42 a15) _ (PV_CBL_FallbackHelpersTotal.add w42 a15) ?_
  intro t114
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 cdgh13 abef13 t114) _ (PV_CBL_FallbackHelpersTotal.round cdgh13 abef13 t114) ?_
  intro cdgh14
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256swap t114) _ (PV_CBL_FallbackHelpersTotal.swap t114) ?_
  intro t214
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 abef13 cdgh14 t214) _ (PV_CBL_FallbackHelpersTotal.round abef13 cdgh14 t214) ?_
  intro abef14
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.schedule w11 w21 w31 w42) _ (PV_CBL_FallbackHelpersTotal.schedule w11 w21 w31 w42) ?_
  intro w02
  refine PV_CBL_FallbackTotal.bind (Array.index_usize a 15#usize) _ (PV_CBL_FallbackTotal.read a 15#usize (by decide)) ?_
  intro a16
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.add w02 a16) _ (PV_CBL_FallbackHelpersTotal.add w02 a16) ?_
  intro t115
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 cdgh14 abef14 t115) _ (PV_CBL_FallbackHelpersTotal.round cdgh14 abef14 t115) ?_
  intro cdgh15
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256swap t115) _ (PV_CBL_FallbackHelpersTotal.swap t115) ?_
  intro t215
  refine PV_CBL_FallbackTotal.bind (PV_CBL_FallbackBlock.sha_fallback_reference.sha256_digest_round_x2 abef14 cdgh15 t215) _ (PV_CBL_FallbackHelpersTotal.round abef14 cdgh15 t215) ?_
  intro abef15
  refine PV_CBL_FallbackTotal.bind (Array.index_usize abef15 0#usize) _ (PV_CBL_FallbackTotal.read abef15 0#usize (by decide)) ?_
  intro a17
  refine PV_CBL_FallbackTotal.bind (Array.index_usize abef15 1#usize) _ (PV_CBL_FallbackTotal.read abef15 1#usize (by decide)) ?_
  intro b
  refine PV_CBL_FallbackTotal.bind (Array.index_usize abef15 2#usize) _ (PV_CBL_FallbackTotal.read abef15 2#usize (by decide)) ?_
  intro e
  refine PV_CBL_FallbackTotal.bind (Array.index_usize abef15 3#usize) _ (PV_CBL_FallbackTotal.read abef15 3#usize (by decide)) ?_
  intro f
  refine PV_CBL_FallbackTotal.bind (Array.index_usize cdgh15 0#usize) _ (PV_CBL_FallbackTotal.read cdgh15 0#usize (by decide)) ?_
  intro c
  refine PV_CBL_FallbackTotal.bind (Array.index_usize cdgh15 1#usize) _ (PV_CBL_FallbackTotal.read cdgh15 1#usize (by decide)) ?_
  intro d
  refine PV_CBL_FallbackTotal.bind (Array.index_usize cdgh15 2#usize) _ (PV_CBL_FallbackTotal.read cdgh15 2#usize (by decide)) ?_
  intro g
  refine PV_CBL_FallbackTotal.bind (Array.index_usize cdgh15 3#usize) _ (PV_CBL_FallbackTotal.read cdgh15 3#usize (by decide)) ?_
  intro h
  refine PV_CBL_FallbackTotal.bind (lift (core.num.U32.wrapping_add i a17)) _ (PV_CBL_FallbackTotal.pure (core.num.U32.wrapping_add i a17)) ?_
  intro i24
  refine PV_CBL_FallbackTotal.bind (Array.update state 0#usize i24) _ (PV_CBL_FallbackTotal.update state 0#usize i24 (by decide)) ?_
  intro state1
  refine PV_CBL_FallbackTotal.bind (Array.index_usize state1 1#usize) _ (PV_CBL_FallbackTotal.read state1 1#usize (by decide)) ?_
  intro i25
  refine PV_CBL_FallbackTotal.bind (lift (core.num.U32.wrapping_add i25 b)) _ (PV_CBL_FallbackTotal.pure (core.num.U32.wrapping_add i25 b)) ?_
  intro i26
  refine PV_CBL_FallbackTotal.bind (Array.update state1 1#usize i26) _ (PV_CBL_FallbackTotal.update state1 1#usize i26 (by decide)) ?_
  intro state2
  refine PV_CBL_FallbackTotal.bind (Array.index_usize state2 2#usize) _ (PV_CBL_FallbackTotal.read state2 2#usize (by decide)) ?_
  intro i27
  refine PV_CBL_FallbackTotal.bind (lift (core.num.U32.wrapping_add i27 c)) _ (PV_CBL_FallbackTotal.pure (core.num.U32.wrapping_add i27 c)) ?_
  intro i28
  refine PV_CBL_FallbackTotal.bind (Array.update state2 2#usize i28) _ (PV_CBL_FallbackTotal.update state2 2#usize i28 (by decide)) ?_
  intro state3
  refine PV_CBL_FallbackTotal.bind (Array.index_usize state3 3#usize) _ (PV_CBL_FallbackTotal.read state3 3#usize (by decide)) ?_
  intro i29
  refine PV_CBL_FallbackTotal.bind (lift (core.num.U32.wrapping_add i29 d)) _ (PV_CBL_FallbackTotal.pure (core.num.U32.wrapping_add i29 d)) ?_
  intro i30
  refine PV_CBL_FallbackTotal.bind (Array.update state3 3#usize i30) _ (PV_CBL_FallbackTotal.update state3 3#usize i30 (by decide)) ?_
  intro state4
  refine PV_CBL_FallbackTotal.bind (Array.index_usize state4 4#usize) _ (PV_CBL_FallbackTotal.read state4 4#usize (by decide)) ?_
  intro i31
  refine PV_CBL_FallbackTotal.bind (lift (core.num.U32.wrapping_add i31 e)) _ (PV_CBL_FallbackTotal.pure (core.num.U32.wrapping_add i31 e)) ?_
  intro i32
  refine PV_CBL_FallbackTotal.bind (Array.update state4 4#usize i32) _ (PV_CBL_FallbackTotal.update state4 4#usize i32 (by decide)) ?_
  intro state5
  refine PV_CBL_FallbackTotal.bind (Array.index_usize state5 5#usize) _ (PV_CBL_FallbackTotal.read state5 5#usize (by decide)) ?_
  intro i33
  refine PV_CBL_FallbackTotal.bind (lift (core.num.U32.wrapping_add i33 f)) _ (PV_CBL_FallbackTotal.pure (core.num.U32.wrapping_add i33 f)) ?_
  intro i34
  refine PV_CBL_FallbackTotal.bind (Array.update state5 5#usize i34) _ (PV_CBL_FallbackTotal.update state5 5#usize i34 (by decide)) ?_
  intro state6
  refine PV_CBL_FallbackTotal.bind (Array.index_usize state6 6#usize) _ (PV_CBL_FallbackTotal.read state6 6#usize (by decide)) ?_
  intro i35
  refine PV_CBL_FallbackTotal.bind (lift (core.num.U32.wrapping_add i35 g)) _ (PV_CBL_FallbackTotal.pure (core.num.U32.wrapping_add i35 g)) ?_
  intro i36
  refine PV_CBL_FallbackTotal.bind (Array.update state6 6#usize i36) _ (PV_CBL_FallbackTotal.update state6 6#usize i36 (by decide)) ?_
  intro state7
  refine PV_CBL_FallbackTotal.bind (Array.index_usize state7 7#usize) _ (PV_CBL_FallbackTotal.read state7 7#usize (by decide)) ?_
  intro i37
  refine PV_CBL_FallbackTotal.bind (lift (core.num.U32.wrapping_add i37 h)) _ (PV_CBL_FallbackTotal.pure (core.num.U32.wrapping_add i37 h)) ?_
  intro i38
  exact PV_CBL_FallbackTotal.update state7 7#usize i38 (by decide)
#print axioms constants
#print axioms total
end R1Z.PV_CBL_FallbackBlockTotal

end
