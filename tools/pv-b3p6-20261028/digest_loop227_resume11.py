"""Named per-level public-digest source control flow, preserving branch/store calls."""
from pathlib import Path
import json,sys
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';O=D/'resume11';files={}
h='namespace PV_B3P_Binding11227\nopen Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Success227\nset_option autoImplicit false\n'
s='import PV_B3P_DigestRead904227\nimport PV_B3P_Ordered227\n'+h+'''
/-- One source level: identical order of selector read, root/frontier read, and digest update. -/
def digest_level11 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q)
    (level : Usize) : Result Digest8Q := do
  let block ← lift (Usize.wrapping_add 34#usize level)
  let shift ← lift (UScalar.cast .U32 level)
  let shifted ← lift (U64.wrapping_shr public1.transition.live_snapshot.next_pair_index shift)
  let bit ← lift (shifted &&& 1#u64)
  if bit = 0#u64 then
    let row ← lift (Usize.wrapping_mul block 16#usize)
    let selector ← reference_copy_terminal.Selectors.row selectors row
    let root ← reference_terminal.empty_root level
    reference_terminal.add_digest_binding output selector openings.z aspis_statement.poseidon2.RATE root true
  else
    let row ← lift (Usize.wrapping_mul block 16#usize)
    let row1 ← lift (Usize.wrapping_add row 12#usize)
    let selector ← reference_copy_terminal.Selectors.row selectors row1
    let frontier ← Array.index_usize public1.transition.live_snapshot.frontier level
    reference_terminal.add_digest_binding output selector openings.z 0#usize frontier false

'''
s+='''theorem count_cast11 (level : Usize) (shift : U32) (h : level.val=shift.val) : UScalar.cast .U32 level = shift := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.cast_val_eq,h]
  exact Nat.mod_eq_of_lt shift.hBounds
#print axioms count_cast11
'''
for i in range(20):s+=f'theorem digest_shift11_{i} : UScalar.cast .U32 {i}#usize = {i}#u32 := count_cast11 _ _ (Eq.refl _)\n#print axioms digest_shift11_{i}\n'
s+='end PV_B3P_Binding11227\n';files['PV_B3P_DigestLevel11227']=s
params='''(public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (output : Digest8Q)'''
for level in range(20):
 i=level+4
 s=f'import PV_B3P_DigestLevel11227\nimport PV_B3P_DigestRead9{i:02}227\n'+h
 s+='attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root Array.index_usize\n'
 s+=f'''theorem digest_level_binding11_{level:02} {params} :
    digest_direct_stage9_{i:02} public1 openings selectors output =
      digest_level11 public1 openings selectors output {level}#usize := by
  unfold digest_direct_stage9_{i:02} digest_read_context9_{i:02} digest_level11
  simp only [digest_shift11_{level},lift,bind_tc_ok]
#print axioms digest_level_binding11_{level:02}
end PV_B3P_Binding11227
''';files[f'PV_B3P_DigestLevel11{level:02}227']=s
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
if '--check'not in sys.argv:(O/'digest-level-modules.json').write_text(json.dumps(list(files),indent=2)+'\n')
