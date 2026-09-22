#!/usr/bin/env python3
"""Offline integrity/boundary audit; does not rerun unchanged SBF gates."""
import argparse,hashlib,json,subprocess,sys
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--assembled',type=Path);a=p.parse_args()
root=Path(__file__).resolve().parent.parent;ev=root/'evidence/r22-native'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((ev/'MANIFEST.json').read_text())
for n,h in m.items():assert sha(ev/n)==h,n
assert not any('keypair' in n or n.endswith(('.so','.regs','.insns')) for n in m)
stage=json.loads((ev/'clean/r18-stage.json').read_text());assert len(stage['files'])==179
ex='docs/research/v8-no-work-100-20260907/experiments/'
for name in ['r22_check.rs','r22_sbf.rs','r22_scalar.rs']:
    assert sha(root/'tools'/name)==stage['files'][ex+name]
assert sha(root/'tools/r22_svm.rs')==sha(ev/'driver/src/main.rs')
if a.assembled:
    for n,h in stage['files'].items():assert sha(a.assembled/n)==h,n
expected={(0,'reference'):786908,(0,'scalar'):768140,(1,'reference'):787096,(1,'scalar'):768067}
receipt=json.loads((ev/'clean/svm/receipt.json').read_text());negative=0
for run in receipt['runs']:
    wire=ev/f"clean/host/generated/world{run['world']}.bin";assert sha(wire)==run['wire_sha256']
    assert len(run['results'])==8
    for r in run['results']:
        assert not r['complete_aspis_verifier'] and r['heap_bytes']==262144 and not r['resource_failure']
        if r['case']=='honest':assert r['accepted'] and r['cu']==expected[run['world'],run['mode']]
        else:assert not r['accepted'] and r['checked_rejection'];negative+=1
assert negative==24
t=json.loads((ev/'clean/trace-analysis.json').read_text());assert t['elf_sha256']==receipt['elf_sha256']
assert t['reference_minus_scalar']['executed_instructions']==18078
for mode in ['reference','scalar']:
    assert t['runs'][mode]['cu']==expected[0,mode] and t['runs'][mode]['tracing_cu_matches_clean']
adj=json.loads(subprocess.check_output([sys.executable,str(root/'tools/check_r22_adjoint.py')],text=True))
assert adj==json.loads((root/'evidence/r22-adjoint.json').read_text())
print(json.dumps({'evidence_files':len(m),'source_pins':len(stage['files']),'assembled_checked':bool(a.assembled),'negative_executions':negative,'exact_adjoint_entries':adj['exact_integer_entries_checked'],'full_verifier_measured':False,'status':'PASS'},indent=2))
