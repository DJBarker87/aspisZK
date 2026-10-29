import PV_B3P_PoseidonSelectorCaller15227
import PV_B3P_ScheduleCaller15227
import PV_B3P_AbsorptionSource15227
import PV_B3P_InterpolationSource15227
import PV_B3P_NativeOccupancy15227
import PV_B3P_NativeInternal15227
import PV_B3P_NativePattern15227
import PV_B3P_NativeActive15227
import PV_B3P_NativePublicDigest15227
import PV_B3P_NativeSumHigh15227
import PV_B3P_NativeProjected15227
import PV_B3P_NativePreweighted15227
import PV_B3P_NativeDigestStore15227
import PV_B3P_NativeSharedRead15227
import PV_B3P_NativeRoundQPlain15227
import PV_B3P_NativeRoundQPacked15227
import PV_B3P_NativeRoundMPlain15227
import PV_B3P_NativeRoundMPacked15227
import PV_B3P_ValueCallerBridge12227
import PV_B3P_MaskNative14227
import PV_B3P_SelectedCorrected14227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Correct14227 PV_B3P_Groups13227
set_option autoImplicit false
noncomputable section
/-- Explicit, jointly satisfiable model instance. All source loops constructed
this round coexist with the corrected mask/layout obligations. Uninstantiated
source bodies keep their MODEL values, never receiving native credit. -/
def joint_source_models15 : ChangedBodies13 :=
  { corrected_model_bodies14 with
    body0 := absorption_source15
    body1 := native_digest_store15
    body3 := @native_preweighted15
    body4 := native_schedule15
    body5 := PV_B3P_Binding12227.value_source12
    body7 := (fun left right => PV_B3P_Loans14227.equality_native14 ⟨0,left⟩ ⟨1,right⟩)
    body8 := native_occupancy15
    body10 := native_poseidon_selectors15
    body11 := native_public_digest15
    body12 := (fun view => PV_B3P_Loans14227.reconstruct_native14 ⟨0,view⟩)
    body15 := (fun selectors ranges => native_sum_high15 ⟨0,selectors⟩ ⟨1,ranges⟩)
    body17 := native_active15
    body18 := native_pattern15
    body19 := PV_B3P_Correct14227.native_mask14
    body23 := native_projected15
    body28 := native_round_QPlain15
    body29 := native_round_MPlain15
    body30 := native_round_MPacked15
    body31 := native_round_QPacked15
    body32 := native_internal15
    body33 := interpolation_source15
    body35 := native_leading15
  }

theorem joint_source_links15 : CorrectedLinks14 joint_source_models15 frozen_calls14 constructor14 57#usize where
  link0 := funext fun low => funext fun fixed => funext fun two => funext fun eight => funext fun nodes => funext fun openings => absorption_source_binding15 low fixed two eight nodes openings
  link1 := funext fun output => funext fun selector => funext fun opened => funext fun start => funext fun expected => funext fun tweak => native_digest_store_binding15 output selector opened start expected tweak
  link2 := corrected_links_witness14.link2
  link3 := native_preweighted_binding15
  link4 := funext fun packed => funext fun public1 => funext fun openings => funext fun selectors => native_schedule_binding15 packed public1 openings selectors
  link5 := funext fun packed => funext fun openings => funext fun selectors => (PV_B3P_Binding12227.value_caller_binding12 packed openings selectors).symm
  link6 := corrected_links_witness14.link6
  link7 := funext fun left => funext fun right => PV_B3P_Loans14227.equality_native_binding14 ⟨0,left⟩ ⟨1,right⟩
  link8 := funext fun input => funext fun output => funext fun expected => funext fun opened => native_occupancy_binding15 input output expected opened
  link9 := corrected_links_witness14.link9
  link10 := funext native_poseidon_selectors_binding15
  link11 := funext fun public1 => funext fun openings => funext fun selectors => native_public_digest_binding15 public1 openings selectors
  link12 := funext fun view => PV_B3P_Loans14227.reconstruct_native_binding14 ⟨0,view⟩
  link13 := corrected_links_witness14.link13
  link14 := corrected_links_witness14.link14
  link15 := fun selectors ranges => native_sum_high_binding15 ⟨0,selectors⟩ ⟨1,ranges⟩
  link16 := corrected_links_witness14.link16
  link17 := funext native_active_binding15
  link18 := funext fun openings => funext fun lambda => native_pattern_binding15 openings lambda
  link19 := PV_B3P_Correct14227.native_mask_link14
  link20 := corrected_links_witness14.link20
  link21 := corrected_links_witness14.link21
  link22 := corrected_links_witness14.link22
  link23 := funext fun openings => funext fun selectors => native_projected_binding15 openings selectors
  link24 := corrected_links_witness14.link24
  link25 := corrected_links_witness14.link25
  link26 := corrected_links_witness14.link26
  link27 := corrected_links_witness14.link27
  link28 := funext fun state => funext fun constants1 => native_round_QPlain_binding15 state constants1
  link29 := funext fun state => funext fun constants1 => native_round_MPlain_binding15 state constants1
  link30 := funext fun state => funext fun constants1 => native_round_MPacked_binding15 state constants1
  link31 := funext fun state => funext fun constants1 => native_round_QPacked_binding15 state constants1
  link32 := funext native_internal_binding15
  link33 := funext fun weights => funext fun c0 => funext fun c1 => funext fun c2 => interpolation_source_binding15 weights c0 c1 c2
  link34 := corrected_links_witness14.link34
  link35 := funext native_leading_binding15
  mask_domain := corrected_links_witness14.mask_domain
  constructor_layout := corrected_links_witness14.constructor_layout
  constructor_native := corrected_links_witness14.constructor_native
#print axioms joint_source_links15
end
end PV_B3P_Native15227
