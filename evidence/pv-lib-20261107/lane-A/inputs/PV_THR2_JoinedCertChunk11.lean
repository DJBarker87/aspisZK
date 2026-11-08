import PV_THR2_F15
import PV_THR2_JoinedCertChunk0
import PV_THR2_JoinedCertChunk1
import PV_THR2_JoinedCertChunk10
import PV_THR2_JoinedCertChunk8
import PV_THR2_JoinedCertDecidable
import PV_THR2_JoinedCertDescriptor
import PV_THR2_OwnUniformSource15Continue165
import PV_THR2_OwnUniformSource15IteratorSyntax
import PV_THR2_OwnUniformSource15Loop93Syntax
import PV_THR2_OwnUniformSource15RangeToLoop
import PV_THR2_OwnUniformSource15To165
import PV_THR2_OwnUniformSource15To165Syntax
import PV_THR2_Source15Continue165
import PV_THR2_Source15RangeToLoop
import PV_THR2_Source15To165

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSource15To165Syntax
open PV_THR2_OwnUniformSource15To165Syntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate for the retained source segment; symbolic instruction
shapes only. No source store evaluation, receiver or endpoint assumption. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node)
    (w : OWNER) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchTrace.Certificate base ctl programs handler 5
      ⟨⟨.running ⟨{activation := a,remaining := [PV_THR2_F15.node5,PV_THR2_F15.node6,PV_THR2_F15.node7,PV_THR2_F15.node8] ++ rest,loops := loops},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertRegionQuietCallCertificate.run base ctl programs handler instructions _ _ _ _ _ _ _ _ w es stack rfl rfl rfl
  · intro i h
    simp only [instructions,List.mem_cons] at h
    rcases h with rfl | rfl | rfl | bad
    all_goals first | trivial | cases bad
  · exact PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)

#print axioms run
end PV_THR2_JoinedCertRegionSource15To165Syntax

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSource15To165
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_THR2_Source15To165
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
      handler ((1+1)+(1+(1+1)))
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 5},parents,s⟩,w,es⟩,stack⟩ := by
  exact PV_THR2_JoinedCertRegionSource15To165Syntax.run _ ctl _ handler s a parents []
    (PV_THR2_F15.live.body.drop 9) w es stack
#print axioms run
end PV_THR2_JoinedCertRegionSource15To165

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSource15IteratorSyntax
open PV_THR2_OwnUniformSource15IteratorSyntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate for the retained source segment; symbolic instruction
shapes only. No source store evaluation, receiver or endpoint assumption. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node)
    (w : OWNER) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchTrace.Certificate base ctl programs handler 3
      ⟨⟨.running ⟨{activation := a,remaining := [PV_THR2_F15.node9,PV_THR2_F15.node10,PV_THR2_F15.node11] ++ [PV_THR2_F15.node48] ++ rest,loops := loops},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertRegionPrefix.take base ctl programs handler (n := instructions.length+1) ?_ 3 (by decide)
  apply PV_THR2_JoinedCertDispatchQuiet.quiet_prefix base ctl programs handler instructions (PV_THR2_F15.node48 :: rest) _ w es stack rfl rfl rfl
  · intro i h
    simp only [instructions,List.mem_cons] at h
    rcases h with rfl | rfl | rfl | bad
    all_goals first | trivial | cases bad
#print axioms run
end PV_THR2_JoinedCertRegionSource15IteratorSyntax

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSource15Continue165
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_THR2_Source15Continue165
/-- Conditional on owner acceptance of amended translator. Hypotheses: exactly
those of the retained source segment below. Generated finite composition using
named source boundaries and syntax certificates; no store evaluation. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (range : Data) (r : Reply OWNER E Data)
    (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchTrace.Certificate base ctl programs handler (steps r)
      (PV_THR2_IntrinsicFullLocal.received base s a parents
        (PV_THR2_F15.live.body.drop 9) PV_THR2_Source15RangeChild.fn165 [range] 5 r es stack) := by
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
      rw [PV_THR2_IntrinsicFullLocal.returned]
      exact PV_THR2_JoinedCertRegionSource15IteratorSyntax.run base ctl programs handler _ a parents []
        (PV_THR2_F15.live.body.drop 13) world (es ++ events) stack
#print axioms run
end PV_THR2_JoinedCertRegionSource15Continue165

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSource15RangeToLoop
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_THR2_Source15RangeToLoop
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
  apply PV_THR2_JoinedCertDispatchTrace.append _ ctl _ handler ((1+1)+(1+(1+1))) _ _ _
    (PV_THR2_Source15To165.run base ctl fallback handler s a parents b w es stack)
  · exact PV_THR2_JoinedCertRegionSource15To165.run base ctl fallback handler s a parents b w es stack
  · exact PV_THR2_JoinedCertRegionSource15Continue165.run _ ctl _ handler _ a parents _ _ es stack
#print axioms run
end PV_THR2_JoinedCertRegionSource15RangeToLoop

set_option autoImplicit false
noncomputable section
namespace PV_THR2_JoinedCertRegionSource15Loop93Syntax
open PV_THR2_OwnUniformSource15Loop93Syntax
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Generated certificate for the retained source segment; symbolic instruction
shapes only. No source store evaluation, receiver or endpoint assumption. -/
theorem run {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node)
    (w : OWNER) (es : List E) (stack : List Config) :
    PV_THR2_JoinedCertDispatchTrace.Certificate base ctl programs handler 7
      ⟨⟨.running ⟨{activation := a,remaining := [PV_THR2_F15.node12,PV_THR2_F15.node13,PV_THR2_F15.node14,PV_THR2_F15.node15,PV_THR2_F15.node16,PV_THR2_F15.node17] ++ rest,loops := loops},parents,s⟩,w,es⟩,stack⟩ := by
  apply PV_THR2_JoinedCertRegionQuietCallCertificate.run base ctl programs handler instructions _ _ _ _ _ _ _ _ w es stack rfl rfl rfl
  · intro i h
    simp only [instructions,List.mem_cons] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | bad
    all_goals first | trivial | cases bad
  · exact PV_THR2_JoinedCertDispatchIds.by_id _ (by decide) (by decide) (by decide)

#print axioms run
end PV_THR2_JoinedCertRegionSource15Loop93Syntax
