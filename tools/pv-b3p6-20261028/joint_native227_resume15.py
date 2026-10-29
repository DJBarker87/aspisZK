from pathlib import Path
L=Path('evidence/pv-b3p6-20261028/lean')
rows=[
 (0,'absorption_source15','funext fun low => funext fun fixed => funext fun two => funext fun eight => funext fun nodes => funext fun openings => absorption_source_binding15 low fixed two eight nodes openings'),
 (1,'native_digest_store15','funext fun output => funext fun selector => funext fun opened => funext fun start => funext fun expected => funext fun tweak => native_digest_store_binding15 output selector opened start expected tweak'),
 (3,'@native_preweighted15','native_preweighted_binding15'),
 (4,'native_schedule15','funext fun packed => funext fun public1 => funext fun openings => funext fun selectors => native_schedule_binding15 packed public1 openings selectors'),
 (5,'PV_B3P_Binding12227.value_source12','funext fun packed => funext fun openings => funext fun selectors => (PV_B3P_Binding12227.value_caller_binding12 packed openings selectors).symm'),
 (7,'(fun left right => PV_B3P_Loans14227.equality_native14 ⟨0,left⟩ ⟨1,right⟩)','funext fun left => funext fun right => PV_B3P_Loans14227.equality_native_binding14 ⟨0,left⟩ ⟨1,right⟩'),
 (8,'native_occupancy15','funext fun input => funext fun output => funext fun expected => funext fun opened => native_occupancy_binding15 input output expected opened'),
 (10,'native_poseidon_selectors15','funext native_poseidon_selectors_binding15'),
 (11,'native_public_digest15','funext fun public1 => funext fun openings => funext fun selectors => native_public_digest_binding15 public1 openings selectors'),
 (12,'(fun view => PV_B3P_Loans14227.reconstruct_native14 ⟨0,view⟩)','funext fun view => PV_B3P_Loans14227.reconstruct_native_binding14 ⟨0,view⟩'),
 (15,'(fun selectors ranges => native_sum_high15 ⟨0,selectors⟩ ⟨1,ranges⟩)','fun selectors ranges => native_sum_high_binding15 ⟨0,selectors⟩ ⟨1,ranges⟩'),
 (17,'native_active15','funext native_active_binding15'),
 (18,'native_pattern15','funext fun openings => funext fun lambda => native_pattern_binding15 openings lambda'),
 (19,'PV_B3P_Correct14227.native_mask14','PV_B3P_Correct14227.native_mask_link14'),
 (23,'native_projected15','funext fun openings => funext fun selectors => native_projected_binding15 openings selectors'),
 (28,'native_round_QPlain15','funext fun state => funext fun constants1 => native_round_QPlain_binding15 state constants1'),
 (29,'native_round_MPlain15','funext fun state => funext fun constants1 => native_round_MPlain_binding15 state constants1'),
 (30,'native_round_MPacked15','funext fun state => funext fun constants1 => native_round_MPacked_binding15 state constants1'),
 (31,'native_round_QPacked15','funext fun state => funext fun constants1 => native_round_QPacked_binding15 state constants1'),
 (32,'native_internal15','funext native_internal_binding15'),
 (33,'interpolation_source15','funext fun weights => funext fun c0 => funext fun c1 => funext fun c2 => interpolation_source_binding15 weights c0 c1 c2'),
 (35,'native_leading15','funext native_leading_binding15')]
imports=['PV_B3P_PoseidonSelectorCaller15227','PV_B3P_ScheduleCaller15227','PV_B3P_AbsorptionSource15227','PV_B3P_InterpolationSource15227','PV_B3P_NativeOccupancy15227','PV_B3P_NativeInternal15227','PV_B3P_NativePattern15227','PV_B3P_NativeActive15227','PV_B3P_NativePublicDigest15227','PV_B3P_NativeSumHigh15227','PV_B3P_NativeProjected15227','PV_B3P_NativePreweighted15227','PV_B3P_NativeDigestStore15227','PV_B3P_NativeSharedRead15227','PV_B3P_NativeRoundQPlain15227','PV_B3P_NativeRoundQPacked15227','PV_B3P_NativeRoundMPlain15227','PV_B3P_NativeRoundMPacked15227','PV_B3P_ValueCallerBridge12227','PV_B3P_MaskNative14227','PV_B3P_SelectedCorrected14227']
s=''.join('import '+m+'\n'for m in imports)+'''namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Correct14227 PV_B3P_Groups13227
set_option autoImplicit false
noncomputable section
/-- Explicit, jointly satisfiable model instance. All source loops constructed
this round coexist with the corrected mask/layout obligations. Uninstantiated
source bodies keep their MODEL values, never receiving native credit. -/
def joint_source_models15 : ChangedBodies13 :=
  { corrected_model_bodies14 with
'''
for i,model,_ in rows:s+=f'    body{i} := {model}\n'
s+='  }\n\ntheorem joint_source_links15 : CorrectedLinks14 joint_source_models15 frozen_calls14 constructor14 57#usize where\n'
lookup={i:proof for i,_,proof in rows}
for i in range(36):s+=f'  link{i} := '+lookup.get(i,f'corrected_links_witness14.link{i}')+'\n'
for field in ['mask_domain','constructor_layout','constructor_native']:s+=f'  {field} := corrected_links_witness14.{field}\n'
s+='#print axioms joint_source_links15\nend\nend PV_B3P_Native15227\n'
(L/'PV_B3P_JointSourceModels15227.lean').write_text(s)
