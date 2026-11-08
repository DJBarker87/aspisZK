import PV_THR2_IntrinsicFrameChain
import PV_THR2_JoinedCertChunk0
import PV_THR2_JoinedCertChunk1
import PV_THR2_JoinedCertChunk10
import PV_THR2_JoinedCertChunk11
import PV_THR2_JoinedCertChunk8
import PV_THR2_JoinedCertDecidable
import PV_THR2_JoinedCertDescriptor
import PV_THR2_OwnUniformChainCertificate
import PV_THR2_OwnUniformSource15AfterHandles93
import PV_THR2_OwnUniformSource15ContinueTo93
import PV_THR2_OwnUniformSource15HandlesTo93
import PV_THR2_OwnUniformSource15Loop93Full
import PV_THR2_OwnUniformSource15RangeTo93
import PV_THR2_Source15AfterHandles93
import PV_THR2_Source15ContinueTo93
import PV_THR2_Source15HandlesTo93
import PV_THR2_Source15Loop93Full
import PV_THR2_Source15RangeTo93

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSource15Loop93Full
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_THR2_Source15Loop93Full
/-- Conditional on owner acceptance of amended translator. Hypotheses: exactly
those of the retained source segment below. Generated finite composition using
named source boundaries and syntax certificates; no store evaluation. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : OWNER) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchTrace.Certificate (PV_THR2_EntryDynamic.carrier base b) ctl
      (PV_THR2_Source208Table.table (PV_THR2_Source15Table.resolve (PV_THR2_OwnInitChildren.resolve fallback)))
      handler (1+(6+1))
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 12},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertDispatchTrace.append _ ctl _ handler 1 (6+1) _ _
    (PV_THR2_Source15LoopEnter.run _ ctl _ handler s a parents w es stack)
  · apply PV_THR2_JoinedCertDispatchTrace.one
    intro c h
    cases h
    first | exact PV_THR2_JoinedCertDispatchShapes.fresh _ rfl | exact (by apply PV_THR2_JoinedCertDispatchShapes.child _ _ _ _ _ rfl rfl; all_goals first | exact (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)).1 | exact (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)).2.1 | exact (PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)).2.2)
  · exact PV_THR2_JoinedCertRegionSource15Loop93Syntax.run _ ctl _ handler s a parents
      [⟨PV_THR2_F15.block47,PV_THR2_F15.live.body.drop 13⟩]
      (PV_THR2_F15.block47.drop 6) w es stack
#print axioms run
end PV_THR2_JoinedCertRegionSource15Loop93Full

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSource15ContinueTo93
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_THR2_Source15ContinueTo93
/-- Conditional on owner acceptance of amended translator. Hypotheses: exactly
those of the retained source segment below. Generated finite composition using
named source boundaries and syntax certificates; no store evaluation. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (range : Data) (b : Bool)
    (r : Reply OWNER E Data) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchTrace.Certificate (PV_THR2_EntryDynamic.carrier base b) ctl
      (PV_THR2_Source208Table.table (PV_THR2_Source15Table.resolve (PV_THR2_OwnInitChildren.resolve fallback)))
      handler (steps r)
      (PV_THR2_Source15Continue165.after (PV_THR2_EntryDynamic.carrier base b) s a parents range r es stack) := by
  rcases r with ⟨answer,world,events⟩
  cases answer with
  | pending => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
  | fault f => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
  | returned result =>
    cases result with
    | fail e => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
    | div => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
    | ok v =>
      simp only [steps,PV_THR2_Source15Continue165.after]
      exact PV_THR2_JoinedCertRegionSource15Loop93Full.run base ctl fallback handler _ a parents b world (es ++ events) stack
#print axioms run
end PV_THR2_JoinedCertRegionSource15ContinueTo93

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSource15RangeTo93
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_THR2_Source15RangeTo93
/-- Conditional on owner acceptance of amended translator. Hypotheses: exactly
those of the retained source segment below. Generated finite composition using
named source boundaries and syntax certificates; no store evaluation. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : OWNER) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchTrace.Certificate
      (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier
        (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier base))) b)
      ctl (PV_THR2_Source208Table.table (PV_THR2_Source15Table.resolve (PV_THR2_OwnInitChildren.resolve fallback)))
      handler (steps handler s w)
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 5},parents,s⟩,w,es⟩,stack⟩ := by
  unfold steps
  apply PV_THR2_JoinedCertDispatchTrace.append _ ctl _ handler _ _ _ _
    (PV_THR2_Source15RangeToLoop.run base ctl fallback handler s a parents b w es stack)
  · exact PV_THR2_JoinedCertRegionSource15RangeToLoop.run base ctl fallback handler s a parents b w es stack
  · exact PV_THR2_JoinedCertRegionSource15ContinueTo93.run _ ctl fallback handler _ a parents _ b _ es stack
#print axioms run
end PV_THR2_JoinedCertRegionSource15RangeTo93

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSource15AfterHandles93
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_THR2_Source15AfterHandles93
/-- Conditional on owner acceptance of amended translator. Hypotheses: exactly
those of the retained source segment below. Generated finite composition using
named source boundaries and syntax certificates; no store evaluation. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : OWNER) (es : List E) (stack : List Config) :
    let r := PV_THR2_Source164OwnPrefix.reply handler (PV_THR2_Source15Call164.entered s a parents) w
    PV_THR2_JoinedCertDispatchTrace.Certificate
      (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier
        (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier base))) b)
      ctl (PV_THR2_Source208Table.table (PV_THR2_Source15Table.resolve (PV_THR2_OwnInitChildren.resolve fallback)))
      handler (steps handler s a parents r)
      (PV_THR2_Source164OwnReturn.after (PV_THR2_RangeLiterals.carrier base) b handler s a parents w es stack) := by
  dsimp only
  unfold PV_THR2_Source164OwnReturn.after
  dsimp only
  unfold PV_THR2_Source164Continue268.after
  generalize hr : PV_THR2_Source164OwnPrefix.reply handler (PV_THR2_Source15Call164.entered s a parents) w = r
  rcases r with ⟨answer,world,events⟩
  cases answer with
  | pending => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
  | fault f => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
  | returned result =>
    cases result with
    | fail e => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
    | div => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
    | ok v =>
      simp only [steps]
      exact PV_THR2_JoinedCertRegionSource15RangeTo93.run base ctl fallback handler (returnedStore s a parents v) a parents b world (es ++ events) stack
#print axioms run
end PV_THR2_JoinedCertRegionSource15AfterHandles93

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSource15HandlesTo93
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_THR2_Source15HandlesTo93
/-- Conditional on owner acceptance of amended translator. Hypotheses: exactly
those of the retained source segment below. Generated finite composition using
named source boundaries and syntax certificates; no store evaluation. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : OWNER) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchTrace.Certificate
      (PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier
        (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier base))) b)
      ctl (PV_THR2_Source208Table.table (PV_THR2_Source15Table.resolve (PV_THR2_OwnInitChildren.resolve fallback)))
      handler (steps handler s a parents w)
      ⟨⟨.running (PV_THR2_Source15Call164.entered s a parents),w,es⟩,stack⟩ := by
  unfold steps
  apply PV_THR2_JoinedCertDispatchTrace.append _ ctl _ handler _ _ _ _
    (PV_THR2_Source164OwnReturn.run (PV_THR2_RangeLiterals.carrier base) ctl fallback handler s a parents b w es stack)
  · exact PV_THR2_JoinedCertRegionSource164OwnReturn.run (PV_THR2_RangeLiterals.carrier base) ctl fallback handler s a parents b w es stack
  · exact PV_THR2_JoinedCertRegionSource15AfterHandles93.run base ctl fallback handler s a parents b w es stack
#print axioms run
end PV_THR2_JoinedCertRegionSource15HandlesTo93

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionChainCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OwnerMachine PV_THR2_IntrinsicFrameChain
abbrev Neutral := PV_THR2_OwnUniformChainCertificate.Neutral
/-- Conditional on owner acceptance of amended translator. Hypothesis: the
straight segment contains no registering instruction. Certify the existing
Chain.run for every symbolic store and every failed binding. Fuel is the
original segment's fuel, never an evaluated concrete-store calculation. -/
theorem run {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (chain : Chain) (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (w : OWNER) (es : List E) (stack : List Config)
    (neutral : Neutral chain) :
    PV_THR2_JoinedCertDispatchTrace.Certificate C K P H (steps C a w chain s)
      ⟨⟨.running ⟨{activation := a,remaining := nodes chain ++ rest,loops := loops},parents,s⟩,w,es⟩,stack⟩ := by
  induction chain generalizing s with
  | done => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
  | storage site live slot next ih =>
    change PV_THR2_JoinedCertDispatchTrace.Certificate C K P H
      (1+steps C a w next (write s ⟨a,slot,[]⟩ none)) _
    apply PV_THR2_JoinedCertDispatchTrace.append C K P H 1 _ _ _
      (PV_THR2_IntrinsicFrameSteps.storage C K P H s a parents loops (nodes next ++ rest) site live slot w es stack)
    · apply PV_THR2_JoinedCertDispatchTrace.one
      intro c eq
      cases eq
      exact PV_THR2_JoinedCertDispatchShapes.fresh _ rfl
    · exact ih _ neutral.2
  | bind site dest expr next ih =>
    change PV_THR2_JoinedCertDispatchTrace.Certificate C K P H
      (1+ match bound C s a dest expr w with | none => 0 | some t => steps C a w next t) _
    apply PV_THR2_JoinedCertDispatchTrace.append C K P H 1 _ _ _
      (PV_THR2_IntrinsicFrameBind.run C K P H s a parents loops (nodes next ++ rest) site dest expr w es stack)
    · apply PV_THR2_JoinedCertDispatchTrace.one
      intro c eq
      cases eq
      exact PV_THR2_JoinedCertDispatchShapes.fresh _ rfl
    · unfold PV_THR2_IntrinsicFrameBind.after
      change PV_THR2_JoinedCertDispatchTrace.Certificate C K P H
        (match bound C s a dest expr w with | none => 0 | some t => steps C a w next t)
        (match bound C s a dest expr w with
         | none => ⟨⟨.undefined (some site) s,w,es⟩,stack⟩
         | some t => ⟨⟨.running ⟨{activation := a,remaining := nodes next ++ rest,loops := loops},parents,t⟩,w,es⟩,stack⟩)
      cases hb : bound C s a dest expr w with
      | none => exact PV_THR2_JoinedCertRegionZero.zero _ _ _ _ _
      | some t => exact ih t neutral
#print axioms run
end PV_THR2_JoinedCertRegionChainCertificate
