import FJg_Part1Trace
import FJj_RegularTrace
import FJc_LowValue
import FJc_LibraFrame
import FIp_FinalSumAliases
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_PairTrace
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NQ NE)
attribute [local irreducible] FIo_Native.weights.powers
  FIo_Native.weights.Weights.pair_loop1 FIo_Native.weights.shared_partials
  FIo_Native.weights.shared_high FIo_Native.weights.grouped_inactive_pair
  FIo_Native.weights.Weights.pair_loop15 FIo_Native.weights.Weights.pair_loop16
  FIo_Native.weights.Weights.pair_loop17
/-- One producing Pair trace through shared_high, inactive write, Libra frame,
and final array. Equal sums are never used to infer equality of arrays. -/
theorem reached [FIo_Native.Allocation] (self : FIo_Native.weights.Weights)
    (alpha : Slice NE) (f : Slice U8) (kappa out : NE)
    (folds : Slice.len alpha=2#usize)
    (guard : FIo_Native.weights.shared_two_point_guard self 2#usize=ok true)
    (run : FIo_Native.weights.Weights.pair self alpha f kappa=ok (.Ok out)) :
    ∃ (n : Usize) (scratch scratchOut : alloc.vec.Vec NQ) (a0 a1 : NE) (ap0 ap1 : Array NE 4#usize) (nativeSelf : FIo_Native.weights.Weights)
      (common : Array NQ 16#usize) (partials : Array NE 4#usize)
      (before highParts lowParts parts k : Array NE 7#usize)
      (low : Array NE 16#usize) (inactive : NE) (libra : Array NE 4#usize)
      (status : core.result.Result Unit FIo_Native.verifier.Error),
      FIo_Native.weights.process_regular_kinds self true alpha f 2#usize n ap0 ap1 scratch
        (Array.repeat 7#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)=
          ok (.Ok (),scratchOut,before) ∧
      Slice.index_usize alpha 0#usize=ok a0 ∧
      FIo_Native.weights.powers 4#usize a0=ok ap0 ∧
      Slice.index_usize alpha 1#usize=ok a1 ∧
      FIo_Native.weights.powers 4#usize a1=ok ap1 ∧
      FIo_Native.weights.Weights.pair_loop1 {start:=0#usize,«end»:=16#usize} self
        (Array.repeat 16#usize FIo_Native.aspis_core.field.QM31.ZERO)=ok (nativeSelf,common) ∧
      nativeSelf=self ∧ FIo_Native.weights.shared_partials f common=ok (.Ok partials) ∧
      FIo_Native.weights.shared_high partials nativeSelf ap0 ap1 before=ok (status,highParts) ∧ status=.Ok () ∧
      FIo_Native.weights.Weights.pair_loop15 {start:=0#usize,«end»:=16#usize} ap0 ap1
        (Array.repeat 16#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)=ok low ∧
      FIo_Native.weights.grouped_inactive_pair nativeSelf f low=ok inactive ∧
      Array.update highParts 0#usize inactive=ok lowParts ∧
      FIo_Native.weights.Weights.pair_loop16 {start:=0#usize,«end»:=4#usize} f lowParts libra=ok parts ∧
      FIo_Native.weights.powers 7#usize kappa=ok k ∧
      FIo_Native.weights.Weights.pair_loop17 {start:=0#usize,«end»:=7#usize} parts k
        FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok out := by
  unfold FIo_Native.weights.Weights.pair at run
  simp only [folds,ite_true,show ¬(2#usize=1#usize) from by decide,ite_false,guard,bind_tc_ok] at run
  repeat' first
  | (solve | cases run)
  | uncase_result
  | head_reduce run
  | split at run
  obtain ⟨a1,h1,hp1⟩ := Port3_PushFrame.bind_success
    (Slice.index_usize alpha 1#usize) (fun a=>FIo_Native.weights.powers 4#usize a) _ (by assumption)
  simp only [FJc_LowValue.seven_alias,FJc_LibraFrame.eight_alias,FIp_FinalSumAliases.nine] at *
  have same := core.result.Result.Ok.inj (Result.ok.inj run)
  cases same
  rename_i cut0 cut1 cut2 cut3 cut4 cut5 cut6 cut7 cut8 cut9 cut10 cut11 cut12 cut13 cut14 initialScratch cut16 cut17 regularOut hregular cut20 cut21 cut22 hcontinued cut24 cut25 cut26 cut27 cut28 cut29 cut30 cut31 cut32 cut33 cut34 cut35 cut36 cut37 cut38 cut39 cut40 cut41 cut42 cut43 cut44 cut45 cut46 cut47 cut48 cut49 cut50 cut51 cut52 cut53 cut54 cut55 cut56
  have st : regularOut.1=.Ok () := FJg_PairProvenance.continued _ _ hcontinued
  have regEq : regularOut=(.Ok (),regularOut.2.1,regularOut.2.2) := Prod.ext st rfl
  have regular := hregular.trans (congrArg Result.ok regEq)
  refine ⟨_,initialScratch,regularOut.2.1,_,a1,_,_,_,_,_,_,_,_,_,_,_,_,_,_,regular,
    by assumption,by assumption,h1,hp1,by assumption,?_,by assumption,by assumption,?_,
    by assumption,by assumption,by assumption,by assumption,by assumption,by assumption⟩
  · exact FJc_SharedSelf.value self _ _ _ _ (by assumption)
  · exact FJg_PairProvenance.continued _ _ (by assumption)
#print axioms reached
end AspisR1.FJj_PairTrace
end
