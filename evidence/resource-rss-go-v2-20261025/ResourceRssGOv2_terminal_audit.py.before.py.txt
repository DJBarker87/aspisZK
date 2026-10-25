"""Offline causal audit of the sole failed host bootstrap, no live replay."""
import builtins
import contextlib
import io
import json
from pathlib import Path
import shlex
import subprocess
import sys
from unittest.mock import patch
import ResourceRssGO_host as host
import ResourceRssGO_local as local

OUT=local.OUT

def load(name):return json.loads((OUT/name).read_text())

def main():
    transport=load('inspect-transport.json')
    executed=transport['source_revision']
    assert executed=='d1edd297ea916ef4438b33e8d34733307feee79b'
    argv=shlex.split(transport['command'][-1])
    assert argv[:4]==['/usr/bin/python3','-I','-B','-c'] and len(argv)==5
    payload=argv[-1]
    original_import=builtins.__import__
    def unstaged(name,*a,**k):
        if name=='ResourceRssGO_guard':raise ModuleNotFoundError("No module named 'ResourceRssGO_guard'")
        return original_import(name,*a,**k)
    output=io.StringIO();failure=None
    with patch.object(builtins,'__import__',unstaged),contextlib.redirect_stdout(output):
        try:exec(payload,{})
        except ModuleNotFoundError as exc:failure=str(exc)
    assert failure=="No module named 'ResourceRssGO_guard'" and output.getvalue()==''
    assert transport['exit']==1 and transport['stdout']==''
    assert transport['stderr'].splitlines()[-1]=='ModuleNotFoundError: '+failure
    assert (OUT/'ATTEMPTED').exists()
    assert not any((OUT/name).exists() for name in ('runtime-inspection.json','manifest.json','RUN_ATTEMPTED','prospective-ordered.json','scope-argv.json','marker.json'))
    seal=load('ResourceRssGO-preparation-seal.json')
    for name,pin in seal['sources'].items():
        if name=='ResourceRssGO_reviewed.json':continue
        raw=subprocess.check_output(['git','show',executed+':tools/resource-rss-go-20261025/'+name])
        assert host.digest(raw)==pin
    current={p.name:host.filepin(p) for p in sorted(Path(__file__).parent.glob('*.py'))}
    old=load('focused-first-receipt.json')
    for name,target in [('ResourceRssGO_tests.py','ResourceRssGO-failed-first-tests.py.txt'),('ResourceRssGO_guard.py','ResourceRssGO-failed-first-guard.py.txt'),('ResourceRssGO_host.py','ResourceRssGO-failed-first-host.py.txt')]:
        assert host.filepin(OUT/target)==old['sources'][name]
    receipt=load('preflight-repair-receipt.json');assert receipt['exit']==0
    for name,pin in receipt['sources'].items():assert current[name]==pin
    result=dict(status='PASS offline causal audit; terminal host preflight failure',
        execution_revision=executed,host_transport_pin=host.filepin(OUT/'inspect-transport.json'),
        payload_pin=host.digest(payload.encode()),failure=failure,host_exit=1,
        host_wall_seconds=transport['wall_seconds'],host_peak_rss='N/A unmeasured',host_swap='N/A unmeasured',
        inherited_host_limits='N/A bootstrap failed before observation',
        new_epoch='USED1/1 before first SSH; no retry authority',prospective='not reached',
        scope=False,GO=False,marker=False,ordered_prospective_GO_replay='N/A no such inputs or reports',
        exact_bootstrap_failure_replayed=True,executed_preparation_seal_matches=True,
        repaired_payload='local test only; no new host identity gate',current_sources=current,
        old_failures='retained unchanged; env UNKNOWN, TID race, Docker reservation',
        resident_guard='new focused synthetic validation only; no host measurement',
        cgroup_controls_peak_swap='N/A no scope',source_revision=local.revision(),
        axioms='N/A',both_security_targets='not established',Kani='59/60 RESERVED')
    with (OUT/'ResourceRssGO-terminal-audit.json').open('x') as f:json.dump(result,f,sort_keys=True,indent=2);f.write('\n')
    print(json.dumps(dict(status='PASS',host_exit=1,scope=False,GO=False,marker=False,epoch='USED1/1')))

if __name__=='__main__':main()
