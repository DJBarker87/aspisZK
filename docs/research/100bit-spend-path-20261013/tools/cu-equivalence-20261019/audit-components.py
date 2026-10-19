#!/usr/bin/env python3
"""Verify exact current sources against focused receipts; never imply full closure."""
from pathlib import Path
import argparse, hashlib, json, resource, subprocess, sys, time

started=time.monotonic()
repo=Path(__file__).resolve().parents[5]
area=repo/'docs/research/100bit-spend-path-20261013'
evidence=area/'evidence/cu-equivalence-20261019'
ap=argparse.ArgumentParser();ap.add_argument('--add',nargs=2,action='append',default=[]);a=ap.parse_args()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
audit_path=evidence/'COMPONENT-AUDIT.json'
audit=json.loads(audit_path.read_text())
for module,attempt in a.add:
    receipt_path=evidence/attempt/'receipt.json'
    receipt=json.loads(receipt_path.read_text())
    audit['successful_targets'][module]=dict(attempt=attempt,
        source_sha256=receipt['source_sha256'],receipt_sha256=sha(receipt_path))
for module,item in audit['successful_targets'].items():
    source=area/'lean'/(module+'.lean')
    receipt_path=evidence/item['attempt']/'receipt.json'
    receipt=json.loads(receipt_path.read_text())
    assert sha(source)==item['source_sha256']==receipt['source_sha256'],module
    assert sha(receipt_path)==item['receipt_sha256'],module
    assert receipt['exit_status']==0,module
    assert 'sorryAx' not in receipt['print_axioms_output'],module
    assert 'error:' not in receipt['print_axioms_output'],module
    assert receipt['process_swaps']==0 and receipt['cgroup_swap_bytes']==0,module
for name in ['Types.lean','Funs.lean']:
    assert (area/'lean/AspisR1CuRho'/name).read_bytes()==(
        Path(__file__).parent/'rho-generated-pushvalue/AspisR1CuRho'/name).read_bytes(),name
finish_check=subprocess.check_output([sys.executable,str(Path(__file__).with_name('emit-finish.py')),
    '--check'],text=True)
audit['finish_emission_layout_check']=json.loads(finish_check)
usage=resource.getrusage(resource.RUSAGE_SELF)
audit['audit_command']=[sys.executable,str(Path(__file__).relative_to(repo)),*sys.argv[1:]]
audit['audit_source_revision']=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip()
audit['audit_wall_seconds']=time.monotonic()-started
audit['audit_peak_rss_bytes']=usage.ru_maxrss if sys.platform=='darwin' else usage.ru_maxrss*1024
audit['audit_process_swaps']=usage.ru_nswap
audit['audit_exit_status']=0
audit['audit_print_axioms']='N/A: receipt/source audit only; per-target axioms outputs checked above'
audit['full_goal_complete']=False
audit_path.write_text(json.dumps(audit,indent=2)+'\n')
print(json.dumps(dict(status=audit['status'],checked_targets=len(audit['successful_targets']),full_goal_complete=False)))
