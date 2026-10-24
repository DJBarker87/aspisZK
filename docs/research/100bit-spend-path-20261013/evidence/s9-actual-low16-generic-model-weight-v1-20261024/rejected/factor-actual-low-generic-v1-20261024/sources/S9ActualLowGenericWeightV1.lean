import S9LowOperatorShapeV1
import S9ActualIndexedPowersSemanticsV1
import S9ActualPairPowersProducerV1
import S9ActualLow16LoopMeaningV1
import S9ArrayReadDropHeadV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActualLowGenericWeightV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualLow16BodyTraceV1 (Powers Low Iter)
open AspisR1S9ActualLow16BodyMeaningV1 (powerValue expectedLow GoodPowers)
open AspisR1S9NativeWideDecodedArithmeticV1 (decode Canonical)
open AspisR1S9FactorArrayEntryV1
open AspisR1S9LowOperatorShapeV1
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev E := AspisWideTower.WideExact

def sourceQuarter : E := AspisR1S9NativeLowScalarArithmeticV1.embed weights.QUARTER

/-- Any bounded actual powers-array observation is fixed by the SAME source
powers4 run. No independent desired power value is assumed. -/
theorem actual_power_value (x : W) (p : Powers) (hx : Canonical x)
    (hp : weights.powers 4#usize x=.ok p) (n : Nat) (hn : n<4) :
    powerValue p n=decode x^n := by
  let nu : Usize := @UScalar.ofNatCore .Usize n (by scalar_tac)
  have hnu : nu.val=n := rfl
  have hi : nu.val<(4#usize).val := by change nu.val<4;omega
  have hr := index_atN p nu hi
  have hv := AspisR1S9ActualIndexedPowersSemanticsV1.actual_powers_four_success_decodes_powers
    x p hx hp nu (atN p nu hi) hr
  have hread := AspisR1S9ActualLow16BodyMeaningV1.power_value_read p nu (atN p nu hi) hr
  change decode (atN p nu hi)=decode x^nu.val at hv
  rw [hnu] at hv hread
  exact hread.trans hv

theorem actual_expected_low_generic (x0 x1 : W) (ap0 ap1 : Powers)
    (hx0 : Canonical x0) (hx1 : Canonical x1)
    (hp0 : weights.powers 4#usize x0=.ok ap0)
    (hp1 : weights.powers 4#usize x1=.ok ap1) (s : Fin 16) :
    expectedLow ap0 ap1 s.val=lowWithQuarter (decode x0) (decode x1) sourceQuarter s := by
  have hpi : AspisR1S9ActualLow16BodyMeaningV1.permutedIndex (s.val%4)<4 := by
    rw [source_permuted_index _ (Nat.mod_lt _ (by decide))]
    exact Nat.mod_lt _ (by decide)
  have hpj : AspisR1S9ActualLow16BodyMeaningV1.permutedIndex (s.val/4)<4 := by
    rw [source_permuted_index _ (by have hs:=s.isLt;omega)]
    exact Nat.mod_lt _ (by decide)
  unfold expectedLow
  rw [actual_power_value x0 ap0 hx0 hp0 _ hpi,actual_power_value x1 ap1 hx1 hp1 _ hpj]
  exact source_low_operator_shape (decode x0) (decode x1) sourceQuarter s

/-- Source low-array total-value notation matches its bounded native read. -/
theorem low_value_read (low : Low) (j : Usize) (value : W)
    (h : Array.index_usize low j=.ok value) :
    (low.val.map decode).getD j.val 0=decode value := by
  have he := AspisR1S9ArrayReadDropHeadV1.array_read_option low j value h
  rw [List.getD_eq_getElem?_getD,List.getElem?_map,he]
  rfl

/-- Both actual low producers are interpreted at the SAME powers4 runs.
The source quarter remains explicit; its generic-quarter identity is separate. -/
theorem actual_low_success_generic (shared : Bool) (x0 x1 : W)
    (ap0 ap1 : Powers) (low out : Low)
    (hx0 : Canonical x0) (hx1 : Canonical x1)
    (hp0 : weights.powers 4#usize x0=.ok ap0)
    (hp1 : weights.powers 4#usize x1=.ok ap1)
    (h : (if shared then weights.Weights.pair_loop7 {start:=0#usize,«end»:=16#usize} ap0 ap1 low
      else weights.Weights.pair_loop15 {start:=0#usize,«end»:=16#usize} ap0 ap1 low)=.ok out) :
    ∀ s : Fin 16,(out.val.map decode).getD s.val 0=
      lowWithQuarter (decode x0) (decode x1) sourceQuarter s := by
  have hc0 := AspisR1S9ActualPairPowersProducerV1.actual_powers_four_native_reads_canonical x0 ap0 hx0 hp0
  have hc1 := AspisR1S9ActualPairPowersProducerV1.actual_powers_four_native_reads_canonical x1 ap1 hx1 hp1
  have hm : AspisR1S9ActualLow16LoopMeaningV1.Prefix ap0 ap1 16 out := by
    cases shared with
    | false => exact (AspisR1S9ActualLow16LoopMeaningV1.actual_low_loop_success
        ap0 ap1 _ low out hc0 hc1 rfl rfl h).1
    | true => exact (AspisR1S9ActualLow16LoopMeaningV1.actual_shared_low_loop_success
        ap0 ap1 _ low out hc0 hc1 rfl rfl h).1
  intro s
  let j : Usize := @UScalar.ofNatCore .Usize s.val (by scalar_tac)
  have hj : j.val<16 := s.isLt
  have hread := index_atN out j hj
  have he := (hm j hj hj).2
  have hv := low_value_read out j (atN out j hj) hread
  change (out.val.map decode).getD s.val 0=decode (atN out j hj) at hv
  change decode (atN out j hj)=expectedLow ap0 ap1 s.val at he
  exact hv.trans (he.trans (actual_expected_low_generic x0 x1 ap0 ap1 hx0 hx1 hp0 hp1 s))

#print axioms actual_power_value
#print axioms actual_expected_low_generic
#print axioms low_value_read
#print axioms actual_low_success_generic
end AspisR1S9ActualLowGenericWeightV1
end
