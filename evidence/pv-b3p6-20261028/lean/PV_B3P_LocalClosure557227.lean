import PV_B3P_JointSourceModels15227
import PV_B3P_SourceAudit543227
import PV_B3P_SourceAudit547227
import PV_B3P_RawSource550227
import PV_B3P_PreparedSource550227
import PV_B3P_InternalPairSource550227
import PV_B3P_DotSource554227
import PV_B3P_ExternalSource554227
import PV_B3P_ConstructorSource554227
import PV_B3P_TerminalSource554227
import PV_B3P_SemanticSource554227
import PV_B3P_CompositionSource554227
namespace PV_B3P_Closure557227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Groups13227 PV_B3P_Correct14227
open PV_B3P_Native15227 PV_B3P_Association543227 PV_B3P_Association546227
open PV_B3P_Association547227 PV_B3P_Association550227 PV_B3P_Association554227
set_option autoImplicit false
noncomputable section
/-- Fixed local interpretations, assembled without selecting any dictionary.
Source provenance and qualified Kani transfers are external evidence; this
structure does not claim a complete native source-cone instance. -/
def local_bodies557 : ChangedBodies13 :=
  { joint_source_models15 with
    body2 := path_dispatch_source554
    body5 := PV_B3P_Binding11227.value_scaling_source11
    body6 := composition_source554
    body7 := PV_B3P_Binding9227.source_equality_value
    body9 := native_path15
    body13 := PV_B3P_Binding11227.sum_context11_semantic_initial_and_absorption
      PV_B3P_Binding11227.source_sum_interval11
    body14 := semantic_source554
    body16 := fresh_transition_reference543
    body20 := dot_source554
    body21 := prepared_source550
    body22 := terminal_constructor57_source554
    body23 := source_projected547
    body24 := expand_source554
    body25 := external_source554
    body26 := source_external_packed547
    body27 := raw_source550
    body31 := source_round_qpacked546
    body32 := source_internal543
    body34 := internal_pair_source550
    body35 := source_leading546 }

/-- All corrected local links coexist. Statement-origin constructor49 is not
identified with the distinct terminal57 constructor used in this cone. -/
theorem local_links557 : CorrectedLinks14 local_bodies557 frozen_calls14 constructor14 57#usize where
  link0 := joint_source_links15.link0
  link1 := joint_source_links15.link1
  link2 := path_dispatch_source_link554
  link3 := joint_source_links15.link3
  link4 := joint_source_links15.link4
  link5 := value_source_link554
  link6 := composition_source_link554
  link7 := equality_source_link543
  link8 := joint_source_links15.link8
  link9 := path_literal_source_link547
  link10 := joint_source_links15.link10
  link11 := joint_source_links15.link11
  link12 := joint_source_links15.link12
  link13 := initial_absorption_source_link554
  link14 := semantic_source_link554
  link15 := joint_source_links15.link15
  link16 := transition_reference_link543
  link17 := joint_source_links15.link17
  link18 := joint_source_links15.link18
  link19 := joint_source_links15.link19
  link20 := dot_source_link554
  link21 := prepared_source_link550
  link22 := joint_source_links15.link22
  link23 := projected_source_link547
  link24 := expand_source_link554
  link25 := external_source_link554
  link26 := external_packed_source_link547
  link27 := raw_source_link550
  link28 := joint_source_links15.link28
  link29 := joint_source_links15.link29
  link30 := joint_source_links15.link30
  link31 := round_qpacked_source_link546
  link32 := internal_source_link543
  link33 := joint_source_links15.link33
  link34 := internal_pair_source_link550
  link35 := leading_source_link546
  mask_domain := joint_source_links15.mask_domain
  constructor_layout := joint_source_links15.constructor_layout
  constructor_native := Eq.trans terminal_constructor57_link554
    joint_source_links15.constructor_native

#print axioms local_links557
end
end PV_B3P_Closure557227
