"""Source-shaped for-range interpreters; small named loop laws only.
The range/dependency implementation catalogue belongs to pv-b3q.
"""
from pathlib import Path
L=Path('evidence/pv-b3p6-20261028/lean')
head='''namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 PV_B3P_Binding11227 PV_B3P_Binding12227 PV_B3P_Binding13227
set_option autoImplicit false
'''
for label,step,typ,finish,law,target in [
 ('QPlain','round_q_step10','aspis_core.field.QM31','reference_poseidon.external_linear_lazy','full_round_source_fold11','full_round'),
 ('QPacked','round_q_step10','aspis_core.field.QM31','reference_poseidon.external_linear_packed','full_round_packed_source_fold11','full_round_packed'),
 ('MPlain','round_m_step10','U32','reference_poseidon.external_linear_lazy','full_round_m31_constants_source_fold11','full_round_m31_constants'),
 ('MPacked','round_m_step10','U32','reference_poseidon.external_linear_packed','full_round_m31_constants_packed_source_fold11','full_round_m31_constants_packed')]:
 mod='PV_B3P_NativeRound'+label+'15227';packed='Packed'in label;size=4 if packed else 16
 s='import PV_B3P_Operations12227\nimport PV_B3P_RangeFold13227\n'+head+f'''
/-- The source range 0..16 runs in increasing order; its lane step preserves
both subfield and whole-element stores in the M31 case. The external layer
is called exactly once, after the range completes. -/
def native_round_{label}15 (state : RoundState10) (constants1 : Array {typ} 16#usize) :
    Result (Array aspis_core.field.QM31 {size}#usize) := do
  let state1 ← range_loop13 ({step} constants1) 0#usize 16#usize state
  {finish} state1

theorem native_round_{label}_binding15 (state : RoundState10)
    (constants1 : Array {typ} 16#usize) :
    native_round_{label}15 state constants1 = reference_poseidon.{target} state constants1 := by
  unfold native_round_{label}15
  rw [range_sixteen13]
  exact ({law} state constants1).symm
#print axioms native_round_{label}_binding15
end PV_B3P_Native15227
'''
 (L/(mod+'.lean')).write_text(s)
# Leading source loop remains a true range loop, not a preselected fold.
s='import PV_B3P_Operations12227\nimport PV_B3P_RangeFold13227\n'+head+'''
def native_leading15 (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) :
    Result (Array aspis_core.field.QM31 4#usize) := do
  let state ← range_loop13 (leading_step12 openings.xor12_z) 0#usize 8#usize openings.z
  leading_finish12 state

theorem leading_indices15 : usize_indices11 8 0#usize =
    [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize] := by
  simp only [usize_indices11,next11_20_0,next11_20_1,next11_20_2,next11_20_3,
    next11_20_4,next11_20_5,next11_20_6,next11_20_7]

theorem native_leading_binding15
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) :
    native_leading15 openings = reference_poseidon.leading_pair_packed openings := by
  unfold native_leading15
  rw [range_as_fold13 _ 0#usize 8#usize 8 _ (by rfl),leading_indices15]
  exact (leading_pair_packed_binding12 openings).symm
#print axioms leading_indices15
#print axioms native_leading_binding15
end PV_B3P_Native15227
'''
(L/'PV_B3P_NativeLeading15227.lean').write_text(s)
