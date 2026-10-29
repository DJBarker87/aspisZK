from pathlib import Path
import json,hashlib
D=Path('evidence/pv-b3p6-20261028');I=json.loads((D/'resume9/body-inventory.json').read_text());F=next(f for f in I['files']if f['family']=='terminal');P=Path(F['source']);assert hashlib.sha256(P.read_bytes()).hexdigest()==F['source_sha256']
rows={r['key']:r for r in I['bodies']if r['family']=='terminal'}
ctor=rows['poseidon_selectors#0']['source'];call=rows['composition_parts#0']['source']
expected=['{','StateOnlyPoseidonSelectors','{','block',':','sum_high','(','selectors',',','&','[','0','.','.','57',']',')',',','local',':','selectors','.','low',',','}','}']
t=ctor['tokens'];assert t[t.index('{'):]==expected
ct=call['tokens'];seq=['poseidon_selectors','(','&','selectors',')'];assert any(ct[i:i+len(seq)]==seq for i in range(len(ct)))
legacy=['StateOnlyPoseidonSelectors',':',':','at_point'];assert not any(ct[i:i+len(legacy)]==legacy for i in range(len(ct)))
r=dict(source=str(P),source_sha256=F['source_sha256'],selected_constructor={'span':[ctor['line'],ctor['end_line']],'tokens_sha256':ctor['sha256'],'step_map':[{'source':'block: sum_high(selectors, &[0..57])','model':'constructor14 selected_blocks14; selected_blocks14=57','remaining':'source sum/range association retained'},{'source':'local: selectors.low','model':'constructor14 copies low array unchanged','remaining':'source Selectors expansion/borrow association retained'}]},exact_caller={'span':[call['line'],call['end_line']],'tokens_sha256':call['sha256'],'call':'evaluate_state_only_poseidon_oracle_projected(&openings, &poseidon_selectors(&selectors))','legacy_constructor_not_called_by_this_expression':True},scope='Local caller-resolution certificate, not an exhaustive deployed reachability/pruning proof; all 79 conservative candidates retained',conclusion='57-block caller selection confirmed; source constructor/sum/expand native binding remains separate',compiler_boundary='V370 / pending owner D381,D386 retained; never T')
(D/'resume14/constructor-caller-resolution.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(dict(local_constructor_blocks=57,exact_caller_checked=True,pruned=0)))
