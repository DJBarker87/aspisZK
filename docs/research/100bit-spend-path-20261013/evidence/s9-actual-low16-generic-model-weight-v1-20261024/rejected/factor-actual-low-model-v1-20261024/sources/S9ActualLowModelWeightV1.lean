import S9ActualLowGenericWeightV1
import S9SourceQuarterModelBridgeV1
import S9TwoDualSourceBaseV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActualLowModelWeightV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualLow16BodyTraceV1 (Powers Low)
open AspisR1S9NativeWideDecodedArithmeticV1 (decode Canonical)
open AspisR1S9LowOperatorShapeV1
open AspisR1S9ActualLowGenericWeightV1
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev E := AspisWideTower.WideExact

theorem generic_low_weight {K : Type} [Field K] (a0 a1 : K) (s : Fin 16) :
    AspisR1S9TwoDualSourceBaseV1.lowWeight a0 a1 s=
      lowWithQuarter a0 a1 AspisR1.RoundPairing.quarter s := by
  unfold lowWithQuarter
  exact AspisR1S9TwoDualSourceBaseV1.low_weight_formula a0 a1 s

theorem low_source_quarter_eq_model : sourceQuarter=(AspisR1.RoundPairing.quarter : E) := by
  exact AspisR1S9SourceQuarterModelBridgeV1.source_quarter_eq_model_quarter

/-- The SAME actual low-array producer equals the generic two-dual-fold low
coefficient. All source power/read/quarter facts are proved dependencies. -/
theorem actual_low_success_model (shared : Bool) (x0 x1 : W)
    (ap0 ap1 : Powers) (low out : Low)
    (hx0 : Canonical x0) (hx1 : Canonical x1)
    (hp0 : weights.powers 4#usize x0=.ok ap0)
    (hp1 : weights.powers 4#usize x1=.ok ap1)
    (h : (if shared then weights.Weights.pair_loop7 {start:=0#usize,«end»:=16#usize} ap0 ap1 low
      else weights.Weights.pair_loop15 {start:=0#usize,«end»:=16#usize} ap0 ap1 low)=.ok out) :
    ∀ s : Fin 16,(out.val.map decode).getD s.val 0=
      AspisR1S9TwoDualSourceBaseV1.lowWeight (decode x0) (decode x1) s := by
  intro s
  have hs := actual_low_success_generic shared x0 x1 ap0 ap1 low out hx0 hx1 hp0 hp1 h s
  have hquarter := congrArg (fun c : E=>lowWithQuarter (decode x0) (decode x1) c s)
    low_source_quarter_eq_model
  exact hs.trans (hquarter.trans (generic_low_weight (decode x0) (decode x1) s).symm)

#print axioms generic_low_weight
#print axioms low_source_quarter_eq_model
#print axioms actual_low_success_model
end AspisR1S9ActualLowModelWeightV1
end
