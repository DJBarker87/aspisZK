import NJU_FieldScalar
set_option autoImplicit false
namespace NKO_LayoutArithmetic
open Aeneas Aeneas.Std Result
theorem weaken {A : Type} (call : Result A) (P Q : A → Prop)
 (spec : call ⦃x=>P x⦄) (law : ∀ x,P x → Q x) : call ⦃x=>Q x⦄ := by
 cases call with
 | fail e => exact spec
 | div => exact spec
 | ok x => exact law x spec
#print axioms weaken
theorem step0 : (10#usize * 28#usize : Result Usize)=ok 280#usize := by
 apply NJU_FieldScalar.eq_of_value
 exact UScalar.mul_spec (x:=10#usize) (y:=28#usize) (by scalar_tac)
theorem step1 : (1#usize + 280#usize : Result Usize)=ok 281#usize := by
 apply NJU_FieldScalar.eq_of_value
 exact UScalar.add_spec (x:=1#usize) (y:=280#usize) (by scalar_tac)
theorem step2 : (87#usize + 29#usize : Result Usize)=ok 116#usize := by
 apply NJU_FieldScalar.eq_of_value
 exact UScalar.add_spec (x:=87#usize) (y:=29#usize) (by scalar_tac)
theorem step3 : (281#usize + 116#usize : Result Usize)=ok 397#usize := by
 apply NJU_FieldScalar.eq_of_value
 exact UScalar.add_spec (x:=281#usize) (y:=116#usize) (by scalar_tac)
theorem step4 : (397#usize + 29#usize : Result Usize)=ok 426#usize := by
 apply NJU_FieldScalar.eq_of_value
 exact UScalar.add_spec (x:=397#usize) (y:=29#usize) (by scalar_tac)
theorem step5 : (16#usize * 426#usize : Result Usize)=ok 6816#usize := by
 apply NJU_FieldScalar.eq_of_value
 have arithmetic : (16#usize).val*(426#usize).val=(6816#usize).val := by
  change 16*426=6816
  omega
 have spec := UScalar.mul_spec (x:=16#usize) (y:=426#usize) (by scalar_tac)
 simpa only [arithmetic] using spec
theorem step6 : (29#usize * 32#usize : Result Usize)=ok 928#usize := by
 apply NJU_FieldScalar.eq_of_value
 exact UScalar.mul_spec (x:=29#usize) (y:=32#usize) (by scalar_tac)
theorem step7 : (12903#usize + 928#usize : Result Usize)=ok 13831#usize := by
 apply NJU_FieldScalar.eq_of_value
 exact UScalar.add_spec (x:=12903#usize) (y:=928#usize) (by scalar_tac)
theorem step8 : (13831#usize - 6816#usize : Result Usize)=ok 7015#usize := by
 apply NJU_FieldScalar.eq_of_value
 have arithmetic : (13831#usize).val-(6816#usize).val=(7015#usize).val := by
  change 13831-6816=7015
  omega
 have spec := UScalar.sub_spec (x:=13831#usize) (y:=6816#usize) (by scalar_tac)
 have projected : (13831#usize-6816#usize : Result Usize) ⦃out=>
  out.val=(13831#usize).val-(6816#usize).val⦄ := weaken _ _ _ spec (fun _ h=>h.1)
 simpa only [arithmetic] using projected
theorem step9 : (16#usize + 7015#usize : Result Usize)=ok 7031#usize := by
 apply NJU_FieldScalar.eq_of_value
 exact UScalar.add_spec (x:=16#usize) (y:=7015#usize) (by scalar_tac)
theorem step10 : (29#usize * 16#usize : Result Usize)=ok 464#usize := by
 apply NJU_FieldScalar.eq_of_value
 exact UScalar.mul_spec (x:=29#usize) (y:=16#usize) (by scalar_tac)
theorem step11 : (7031#usize + 464#usize : Result Usize)=ok 7495#usize := by
 apply NJU_FieldScalar.eq_of_value
 exact UScalar.add_spec (x:=7031#usize) (y:=464#usize) (by scalar_tac)
theorem step12 : (7495#usize + 32#usize : Result Usize)=ok 7527#usize := by
 apply NJU_FieldScalar.eq_of_value
 exact UScalar.add_spec (x:=7495#usize) (y:=32#usize) (by scalar_tac)
theorem step13 : (7527#usize + 224#usize : Result Usize)=ok 7751#usize := by
 apply NJU_FieldScalar.eq_of_value
 exact UScalar.add_spec (x:=7527#usize) (y:=224#usize) (by scalar_tac)
theorem step14 : (7751#usize + 32#usize : Result Usize)=ok 7783#usize := by
 apply NJU_FieldScalar.eq_of_value
 exact UScalar.add_spec (x:=7751#usize) (y:=32#usize) (by scalar_tac)
theorem step15 : (7783#usize + 224#usize : Result Usize)=ok 8007#usize := by
 apply NJU_FieldScalar.eq_of_value
 exact UScalar.add_spec (x:=7783#usize) (y:=224#usize) (by scalar_tac)
theorem step16 : (64#usize * 32#usize : Result Usize)=ok 2048#usize := by
 apply NJU_FieldScalar.eq_of_value
 exact UScalar.mul_spec (x:=64#usize) (y:=32#usize) (by scalar_tac)
theorem step17 : (8007#usize + 2048#usize : Result Usize)=ok 10055#usize := by
 apply NJU_FieldScalar.eq_of_value
 exact UScalar.add_spec (x:=8007#usize) (y:=2048#usize) (by scalar_tac)
#print axioms step0
#print axioms step1
#print axioms step2
#print axioms step3
#print axioms step4
#print axioms step5
#print axioms step6
#print axioms step7
#print axioms step8
#print axioms step9
#print axioms step10
#print axioms step11
#print axioms step12
#print axioms step13
#print axioms step14
#print axioms step15
#print axioms step16
#print axioms step17
end NKO_LayoutArithmetic
