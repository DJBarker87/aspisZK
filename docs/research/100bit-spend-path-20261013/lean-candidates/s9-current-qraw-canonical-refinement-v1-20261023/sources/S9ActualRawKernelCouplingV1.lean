import S9ActualRawKernelsV1
import S9CheckedMulWrappingSuccessV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActualRawKernelCouplingV1
open AspisR1S9ActualRawKernelsV1 AspisR1S9CheckedMulWrappingSuccessV1
private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B)
    (out : B) (h : (do let a ← m; f a) = .ok out) :
    ∃ a, m = .ok a ∧ f a = .ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok a => exact ⟨a,rfl,h⟩
private theorem shift31 (x : U64) : x >>> 31#i32 = .ok (U64.wrapping_shr x 31#u32) := by rfl

theorem actual_p_same : AspisR1S9ActualRawCutV1.fast_pairing.canonical.P = AspisR1CanonicalQRawUnified.canonical.P := by
  unfold AspisR1S9ActualRawCutV1.fast_pairing.canonical.P AspisR1CanonicalQRawUnified.canonical.P
  rfl

theorem actual_pp_same : AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw.PP = AspisR1CanonicalQRawUnified.canonical.Q.raw.PP := by
  unfold AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw.PP AspisR1CanonicalQRawUnified.canonical.Q.raw.PP
  rw [actual_p_same]

theorem actual_partial_same (state : Unit) (x : U64) :
    AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnTupleU64U64.call state x =
      AspisR1CanonicalQRawUnified.canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call state x := by
  unfold AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnTupleU64U64.call
    AspisR1CanonicalQRawUnified.canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call
  simp only [actual_p_same,shift31,lift,bind_tc_ok]

/-- SAME retained checked-kernel success supplies every checked product.
Each successful product equals the actual release wrapping product; the
actual PP and partial calls are explicitly identified. No no-overflow or
independent actual-kernel-success premise is introduced. The public canonical
source theorem derives this one premise using existing S5 totality. -/
theorem checked_kernel_success_actual (a b c d e f g h : U64) (out : R4)
    (hrun : checkedKernel a b c d e f g h = .ok out) :
    actualKernel a b c d e f g h = .ok out := by
  unfold checkedKernel at hrun
  simp only [lift,bind_tc_ok] at hrun
  obtain ⟨cg,h_cg,hrun⟩ := bind_success _ _ _ hrun
  have w_cg := u64_mul_success _ _ _ h_cg
  obtain ⟨pp,h_pp,hrun⟩ := bind_success _ _ _ hrun
  obtain ⟨dh,h_dh,hrun⟩ := bind_success _ _ _ hrun
  have w_dh := u64_mul_success _ _ _ h_dh
  obtain ⟨u,h_u,hrun⟩ := bind_success _ _ _ hrun
  obtain ⟨ch,h_ch,hrun⟩ := bind_success _ _ _ hrun
  have w_ch := u64_mul_success _ _ _ h_ch
  obtain ⟨dg,h_dg,hrun⟩ := bind_success _ _ _ hrun
  have w_dg := u64_mul_success _ _ _ h_dg
  obtain ⟨v,h_v,hrun⟩ := bind_success _ _ _ hrun
  obtain ⟨ae,h_ae,hrun⟩ := bind_success _ _ _ hrun
  have w_ae := u64_mul_success _ _ _ h_ae
  obtain ⟨bf,h_bf,hrun⟩ := bind_success _ _ _ hrun
  have w_bf := u64_mul_success _ _ _ h_bf
  obtain ⟨twoU,h_twoU,hrun⟩ := bind_success _ _ _ hrun
  have w_twoU := u64_mul_success _ _ _ h_twoU
  obtain ⟨threeP,h_threeP,hrun⟩ := bind_success _ _ _ hrun
  have w_threeP := u64_mul_success _ _ _ h_threeP
  obtain ⟨af,h_af,hrun⟩ := bind_success _ _ _ hrun
  have w_af := u64_mul_success _ _ _ h_af
  obtain ⟨be,h_be,hrun⟩ := bind_success _ _ _ hrun
  have w_be := u64_mul_success _ _ _ h_be
  obtain ⟨twoV,h_twoV,hrun⟩ := bind_success _ _ _ hrun
  have w_twoV := u64_mul_success _ _ _ h_twoV
  obtain ⟨ag,h_ag,hrun⟩ := bind_success _ _ _ hrun
  have w_ag := u64_mul_success _ _ _ h_ag
  obtain ⟨ce,h_ce,hrun⟩ := bind_success _ _ _ hrun
  have w_ce := u64_mul_success _ _ _ h_ce
  obtain ⟨twoPP,h_twoPP,hrun⟩ := bind_success _ _ _ hrun
  have w_twoPP := u64_mul_success _ _ _ h_twoPP
  obtain ⟨bh,h_bh,hrun⟩ := bind_success _ _ _ hrun
  have w_bh := u64_mul_success _ _ _ h_bh
  obtain ⟨df,h_df,hrun⟩ := bind_success _ _ _ hrun
  have w_df := u64_mul_success _ _ _ h_df
  obtain ⟨ah,h_ah,hrun⟩ := bind_success _ _ _ hrun
  have w_ah := u64_mul_success _ _ _ h_ah
  obtain ⟨bg,h_bg,hrun⟩ := bind_success _ _ _ hrun
  have w_bg := u64_mul_success _ _ _ h_bg
  obtain ⟨cf,h_cf,hrun⟩ := bind_success _ _ _ hrun
  have w_cf := u64_mul_success _ _ _ h_cf
  obtain ⟨de,h_de,hrun⟩ := bind_success _ _ _ hrun
  have w_de := u64_mul_success _ _ _ h_de
  unfold actualKernel
  simp only [lift,bind_tc_ok,actual_p_same,actual_pp_same,actual_partial_same,
    w_cg,h_pp,w_dh,h_u,w_ch,w_dg,h_v,w_ae,w_bf,w_twoU,w_threeP,w_af,w_be,w_twoV,w_ag,w_ce,w_twoPP,w_bh,w_df,w_ah,w_bg,w_cf,w_de]
  exact hrun

#print axioms actual_p_same
#print axioms actual_pp_same
#print axioms actual_partial_same
#print axioms checked_kernel_success_actual
end AspisR1S9ActualRawKernelCouplingV1
