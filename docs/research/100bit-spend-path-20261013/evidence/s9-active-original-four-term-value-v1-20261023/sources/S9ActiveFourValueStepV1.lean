import S9ActiveSameInputV1
import S9ActiveFourCanonicalV1
import S9ArrayReadDropHeadV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9ActiveFourValueStepV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9NativeS3WeightBodyV1 (W Can decode)
open AspisR1S9ActiveFourCanonicalV1 (Parts Libra R)
open AspisR1S9FactorArrayEntryV1
open AspisR1S9NativeS3CoefficientBodyV1 (C)
abbrev E := AspisWideTower.WideExact

def cell4 (parts : Parts) : W := atN parts 4#usize (by decide)
def libraValue (libra : Libra) (n : Nat) : E := ((libra.val.map decode).drop n).headD 0

theorem update_four_cell_value (parts out : Parts) (value : W)
    (h : Array.update parts 4#usize value=.ok out) : cell4 out=value := by
  have he := accepted_update_eq_set parts 4#usize (by decide) value out h
  subst out
  unfold cell4
  rw [atN_set parts 4#usize 4#usize value (by decide) (by decide)] <;> rfl

/-- SAME actual active step supplies its strict field read, coefficient read,
mul/add and write. Data is identified with SAME inactive strict-input stream;
there is no independent hfields, product, sum or child-success premise. -/
theorem active_cont_same_input_value (f : Slice U8) (coefficients : C)
    (hbytes : 2048≤f.val.length)
    (hcoeff : weights.s2_grouped_inactive_pair_loop0 {start:=0#usize,«end»:=64#usize} f
      (Array.repeat 12#usize aspis_core.field.wide_exact.WideExact.ZERO)=.ok coefficients)
    (libra : Libra) (iter iterOut : R) (parts out : Parts)
    (hend : iter.end.val≤4) (hcarry : Can (cell4 parts))
    (hlibra : AspisR1S9NativeArrayCanonicalV1.ReadsCanonical libra)
    (hbody : weights.Weights.pair_loop8.body f libra iter parts=.ok (.cont (iterOut,out))) :
    ∃ j : Usize,core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (some j,iterOut) ∧
      j.val<4 ∧ Can (cell4 out) ∧ decode (cell4 out)=decode (cell4 parts)+
        AspisR1S9NativeS3ZeroPrefixV1.successfulInput f coefficients hbytes hcoeff j.val *
          libraValue libra j.val := by
  obtain ⟨j,carry,value,coefficient,product,total,hn,hcarryRead,hfield,hcf,hmul,hadd,hu⟩ :=
    AspisR1S9ActiveFourCanonicalV1.body_cont_source f libra iter iterOut parts out hbody
  have hj := (AspisR1S9ActualDotRangeBoundsV1.range_next_index_bounds iter iterOut j hn).2.1
  have hj4 : j.val<4 := by omega
  obtain ⟨cvalue,hvalue⟩ := AspisR1S9ActiveSameInputV1.actual_field_same_coefficient_input
    f coefficients hbytes hcoeff j value (by omega) hfield
  have hcarryEq : carry=cell4 parts := accepted_index_eq_atN parts 4#usize (by decide) carry hcarryRead
  have ccarry : Can carry := by simpa only [hcarryEq] using hcarry
  obtain ⟨cproduct,hproduct⟩ := AspisR1S9NativeWideDecodedArithmeticV1.actual_mul_success_decoded
    value coefficient product cvalue (hlibra j coefficient hcf) hmul
  obtain ⟨ctotal,htotal⟩ := AspisR1S9NativeWideDecodedArithmeticV1.actual_add_success_decoded
    carry product total ccarry cproduct hadd
  change decode product=decode value*decode coefficient at hproduct
  change decode total=decode carry+decode product at htotal
  rw [hproduct,hvalue,hcarryEq] at htotal
  have hcoefficient := AspisR1S9ArrayReadDropHeadV1.array_read_map_drop_head decode 0 libra j coefficient hcf
  have hcell := update_four_cell_value parts out total hu
  refine ⟨j,hn,hj4,?_,?_⟩
  · simpa only [hcell] using ctotal
  · change decode (cell4 out)=decode (cell4 parts)+_ *
      ((libra.val.map decode).drop j.val).headD 0
    rw [hcell,hcoefficient]
    exact htotal

#print axioms update_four_cell_value
#print axioms active_cont_same_input_value
end AspisR1S9ActiveFourValueStepV1
