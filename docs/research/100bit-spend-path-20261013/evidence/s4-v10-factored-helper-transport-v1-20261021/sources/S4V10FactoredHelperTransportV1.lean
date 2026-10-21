import S4V10HeadValueTransportV1
import S4V10TailMapRootV1
import S4FixedTailProgramEqualityRootV1

open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1FastDotsV10FactoredHelperTransportV1
open AspisR1FastDotsV10HeadValueTransportV1
open AspisR1FastDotsV10CarrierMapV1
open AspisR1FastDotsV10TypedInnerBodyOpsV1
abbrev CurrentOps := AspisR1FastDotsCurrent.FourDotsOps
abbrev V10Wide := AspisR1FastDotsMinimalFixedCallsV10.aspis_core.field.wide_exact.WideExact
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev Usize := Aeneas.Std.Usize

def mapRes {A B : Type} (f : A → B) : Result A → Result B
| .ok x => .ok (f x)
| .fail e => .fail e
| .div => .div

private theorem mapRes_comp_id {A B : Type} (f : A → B) (g : B → A)
    (h : ∀ a, g (f a) = a) (r : Result A) : mapRes g (mapRes f r) = r := by
  cases r with
  | ok a => simp [mapRes, h a]
  | fail e => rfl
  | div => rfl

def v10FactoredHelper (ops : CurrentOps) (q : Array Std.U8 608#usize)
    (g : Array V10Wide 29#usize) (slot : Usize) : Result V10Wide := do
  let value ← v10HeadValue ops q g slot
  AspisR1FastDotsV10TailMapRootV1.v10Tail ops q g slot value

def fixedFactoredHelper (ops : CurrentOps) (q : Array Std.U8 608#usize)
    (g : Array V10Wide 29#usize) (slot : Usize) : Result Wide := do
  let value ← fixedHeadValue ops q g slot
  AspisR1FastDotsFixedTailProgramEqualityRootV1.fixedTail ops q (mapWideArray g) slot value

private theorem v10Tail_from_current (ops : CurrentOps) (q : Array Std.U8 608#usize)
    (g : Array V10Wide 29#usize) (slot : Usize) (value : V10Wide) :
    AspisR1FastDotsV10TailMapRootV1.v10Tail ops q g slot value =
      mapRes wideFromEbyK (AspisR1FastDotsFixedTailProgramEqualityRootV1.fixedTail
        ops q (mapWideArray g) slot (wideToEbyK value)) := by
  have hroot : mapRes wideToEbyK
      (AspisR1FastDotsV10TailMapRootV1.v10Tail ops q g slot value) =
      AspisR1FastDotsFixedTailProgramEqualityRootV1.fixedTail
        ops q (mapWideArray g) slot (wideToEbyK value) := by
    exact (AspisR1FastDotsV10TailMapRootV1.v10Tail_to_current ops q g slot value)
  have hround := mapRes_comp_id wideFromEbyK wideToEbyK wide_roundtrip'
    (AspisR1FastDotsFixedTailProgramEqualityRootV1.fixedTail
      ops q (mapWideArray g) slot (wideToEbyK value))
  have hmap : mapRes wideToEbyK
      (mapRes wideFromEbyK
        (AspisR1FastDotsFixedTailProgramEqualityRootV1.fixedTail
          ops q (mapWideArray g) slot (wideToEbyK value))) =
      mapRes wideToEbyK
        (AspisR1FastDotsV10TailMapRootV1.v10Tail ops q g slot value) := by
    exact hround.trans hroot.symm
  have hinj : ∀ {x y : Result V10Wide}, mapRes wideToEbyK x = mapRes wideToEbyK y → x = y := by
    intro x y hxy
    cases x with
    | ok a => cases y with
      | ok b =>
        simp only [mapRes] at hxy
        have hab : wideToEbyK a = wideToEbyK b := by injection hxy
        have h := congrArg wideFromEbyK hab
        simpa only [wide_roundtrip] using congrArg Result.ok h
      | fail e => simp [mapRes] at hxy
      | div => simp [mapRes] at hxy
    | fail e => cases y <;> simp_all [mapRes]
    | div => cases y <;> simp_all [mapRes]
  have htail := hinj hmap
  exact htail.symm

theorem factored_helper_eq_fixed (ops : CurrentOps) (q : Array Std.U8 608#usize)
    (g : Array V10Wide 29#usize) (slot : Usize) :
    v10FactoredHelper ops q g slot = mapRes wideFromEbyK (fixedFactoredHelper ops q g slot) := by
  unfold v10FactoredHelper fixedFactoredHelper
  exact AspisR1FastDotsV10HeadValueTransportV1.bind_map_inverse
    wideFromEbyK wideToEbyK wide_roundtrip'
    (v10HeadValue ops q g slot) (fixedHeadValue ops q g slot)
    (head_value_eq_fixed ops q g slot)
    (AspisR1FastDotsV10TailMapRootV1.v10Tail ops q g slot)
    (AspisR1FastDotsFixedTailProgramEqualityRootV1.fixedTail ops q (mapWideArray g) slot)
    (v10Tail_from_current ops q g slot)

#print axioms factored_helper_eq_fixed
end AspisR1FastDotsV10FactoredHelperTransportV1
