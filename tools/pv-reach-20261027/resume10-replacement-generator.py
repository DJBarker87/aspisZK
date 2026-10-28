"""Permanent symbolic replacements from retained failed candidates.
--check validates the accepted sources without changing or recompiling them.
The original sources remain intact; no recurrence or native body is generated.
"""
from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';check='--check' in sys.argv

def emit(name,text):
 p=L/(name+'.lean')
 if check:assert p.read_text()==text,name
 else:p.write_text(text)

for i in range(2,8):
 old=f'PV_RE_LayoutPrefix10{i:02d}';s=(L/(old+'.lean')).read_text().replace(old,old+'B')
 for j in [1,4,5,6]:s=s.replace(f'  rw [h{j}]\n',f'  rw [h{j}]\n  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]\n')
 emit(old+'B',s)
s=(L/'PV_RE_MaterialCellsB10.lean').read_text().replace('PV_RE_MaterialCellsB10','PV_RE_MaterialCellsC10');a=s.index('  rw [hm]\n');b=s.index('  exact ⟨_,rfl⟩',a)
s=s[:a]+'''  simp only [hm,hf,bind_tc_ok,ProverRwOuterContextModel.context,
    Bool.false_eq_true,if_false]
'''+s[b:];emit('PV_RE_MaterialCellsC10',s)
s=(L/'PV_RE_AttemptClone10.lean').read_text().replace('PV_RE_AttemptClone10','PV_RE_AttemptCloneB10')
s=s.replace('  rw [reservation]\n','  simp only [bind_tc_ok]\n  rw [reservation]\n  simp only [bind_tc_ok]\n').replace('  rw [mapped]\n','  rw [mapped]\n  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]\n');emit('PV_RE_AttemptCloneB10',s)
s=(L/'PV_RE_StoreOpenErrors10.lean').read_text().replace('R1Z.PV_RE_StoreOpenErrors10','R1Z.PV_RE_StoreOpenErrorsB10').replace('= .ok true)) :','= .ok true) :').replace('= .ok false)) :','= .ok false) :');emit('PV_RE_StoreOpenErrorsB10',s)
s=(L/'PV_RE_AfterSuccess10.lean').read_text().replace('PV_RE_AfterSuccess10','PV_RE_AfterSuccessB10')
s=s.replace('''      .ok (.Ok ({mask_nonce := secret.mask_nonce,precommit_binding := binding,
        reserved_context := context,leaf_salt_seed := secret.leaf_salt_seed,
        source_mask_seed := wrapped},material),store1)''','''      .ok (.Ok ({mask_nonce := secret.mask_nonce, precommit_binding := binding, reserved_context := context, leaf_salt_seed := secret.leaf_salt_seed, source_mask_seed := wrapped},material),store1)''');emit('PV_RE_AfterSuccessB10',s)
print('10 replacement source templates match; retained failed inputs unchanged.' if check else 'Wrote 10 symbolic replacement sources.')
