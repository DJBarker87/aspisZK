"""Frozen-source argument inventory with matched mutations; no native credit."""
from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
paths=['programs/aspis-pool/src/pair_forest.rs','programs/aspis-pool/src/pair_forest_dispatch.rs','programs/r1-cost-probe/src/pool_route.rs','programs/r1-cost-probe/src/lib.rs']
source={p:subprocess.check_output(['git','show',REV+':'+p],text=True) for p in paths}
a=source[paths[0]];b=source[paths[1]];c=source[paths[2]];d=source[paths[3]]
start=a.index('pub(crate) fn process_pair_forest_terminal_with_verifier_v1');end=a.index('    let result = authenticated.value();',start);prefix=a[start:end]
checks=[('master_account','let master_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;'),('checkpoint_account','let checkpoint_account = accounts.get(1).ok_or(ProgramError::NotEnoughAccountKeys)?;'),('lane_account','let lane_account = accounts.get(2).ok_or(ProgramError::NotEnoughAccountKeys)?;'),('request_decode','let request = decode_terminal_request_box_v1(request_bytes)?;'),('registry_window','&accounts[layout.registry_start..layout.registry_start + 2]'),('verifier_program','&accounts[layout.verifier_index]'),('proof_account','&accounts[layout.proof_index]'),('checkpoint_option','.map(|index| &accounts[index])'),('same_request','        &request,\n        current_slot,\n    )?;')]
def check(s):return all(s.count(text)==1 for _,text in checks)
assert check(prefix)
controls=[]
for label,text in checks:
 mutated=prefix.replace(text,text.replace('accounts','different_accounts') if 'accounts' in text else text.replace('request','different_request'),1)
 assert mutated!=prefix and not check(mutated),label
 controls.append(dict(name=label,rejected=True,mutated_sha256=hashlib.sha256(mutated.encode()).hexdigest()))
assert 'data == [3, 10] || data == [3, 11] || data.starts_with(b"ASQ8")' in c
assert 'if !pool_route::admitted(data)' in d
assert 'data: plan.request_bytes,' in b and 'program_id: plan.selected_verifier,' in b
assert 'runtime.clear_return_data();\n    runtime.invoke(&instruction, &infos)?;' in b
out=dict(revision=REV,source_pins={p:hashlib.sha256(s.encode()).hexdigest() for p,s in source.items()},prefix_sha256=hashlib.sha256(prefix.encode()).hexdigest(),checks=[label for label,_ in checks],controls=controls,classification='SOURCE INVENTORY ONLY; does not discharge ruling(y)(1), production native prefix remains OPEN',call_order='Pool admission -> plan -> invoke -> verifier pool_route admission')
(E/'NFV_PREFIX_SOURCE.json').write_text(json.dumps(out,indent=1)+'\n')
print(json.dumps(dict(checks=len(checks),mutations_rejected=len(controls),native_credit=False)))
