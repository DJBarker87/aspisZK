"""Offline new-failure assessment; no alternate decision or live operation."""
import ast
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time
import ResourceStableGO_adapter as adapter
import ResourceStableGO_host as host

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'evidence/resource-stable-go-20261025'
START=time.monotonic()

def load(name):return json.loads((OUT/name).read_bytes())

def main():
    events=[]
    for p in sorted(OUT.glob('prospective-ordered-*.json')):events.extend(json.loads(p.read_bytes()))
    docker=next(e for e in events if e['kind']=='command' and e['command']==['docker','ps','-q'])
    assert docker['exit']==2 and 'failed to reserve page summary memory' in docker['stderr']
    ps=next(e for e in events if e['kind']=='command' and e['command']==adapter.COMMANDS[0])
    assert ps['exit']==0
    rss_snapshot=sum(int(line.split()[2])*1024 for line in ps['stdout'].splitlines()[1:])
    report=load('prospective-report-summary.json')
    assert report['decision']['allowed'] is False
    assert report['decision']['collection_failures']['visibility']['type']=='CalledProcessError'
    # Independent OFFLINE validation of retained successful scans only. This is
    # not an alternative prospective admission, nor a numeric margin calculation.
    snapshots=report['snapshots'];collectors={};frontiers={}
    for label,snapshot in snapshots.items():
        observation=adapter.c.observe(snapshot)
        collectors[label]=adapter.policy.collector(snapshot)
        frontiers[label]=dict(paths=observation['frontier'],full_cap_reservation_bytes=observation['bounded_reserved_bytes'])
    structure_same=adapter.policy.structural(snapshots['before'])==adapter.policy.structural(snapshots['after'])
    # Source evidence of the new inherited virtual-address constraint. No host
    # reread and no claim of proven exclusive causality from this static check.
    source=Path(host.__file__).read_text();tree=ast.parse(source)
    limits=[n for n in ast.walk(tree) if isinstance(n,ast.Call) and ast.unparse(n.func)=='resource.setrlimit']
    assert len(limits)==1 and 'RLIMIT_AS' in ast.unparse(limits[0])
    run=next(n for n in ast.walk(tree) if isinstance(n,ast.FunctionDef) and n.name=='visibility') if False else None
    assert not any((OUT/name).exists() for name in ('scope-argv.json','scope-child.json','marker.json','go-controls-before.json','inside-scope-report.json'))
    outcome=dict(status='TERMINAL PROSPECTIVE DENY; new allocation exhausted',events=len(events),
        docker=dict(command=docker['command'],exit=docker['exit'],stderr_pin=host.digest(docker['stderr'].encode()),first_line=docker['stderr'].splitlines()[0]),
        source_assessment=dict(added_limit=ast.unparse(limits[0]),kind='virtual-address-space limit, not RSS',
            inheritance='subprocesses inherit parent resource limits; no child reset in recorded runner',
            inference='new inherited 512MiB RLIMIT_AS is the likely cause of Go virtual reservation failure; exclusive cause not independently proven',
            prior_runner_had_limit=False,old_failure_history='initial env field UNKNOWN; v2 TID3871412 race; unchanged'),
        snapshots_offline_validated=True,collector_identity_equal=collectors['before']==collectors['after'],
        structural_projection_equal=structure_same,collector_identities=collectors,frontiers=frontiers,
        policy_margin='N/A; legacy visibility failed; no counterfactual admission evaluated',
        raw_ps_process_sum_snapshot_bytes=rss_snapshot,process_sum_kind='single ps snapshot, not aggregate/cgroup peak',
        recorded_metrics_aggregate_rss_bytes=load('prospective-metrics.json')['aggregate_rss_bytes'],
        recorded_zero_assessment='unavailable placeholder because original_legacy is None; not a zero-RSS observation',
        actual_scope=False,actual_GO=False,marker=False,effective_scope_controls='N/A; no scope',
        cgroup_peak='N/A; no scope',scope_swap='N/A; no scope',
        no_retry=True,print_axioms='N/A',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
        command=[sys.executable,'-B',str(Path(__file__).resolve())],exit=0,wall_seconds=time.monotonic()-START,
        peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*(1 if sys.platform=='darwin' else 1024),swap=resource.getrusage(resource.RUSAGE_SELF).ru_nswap)
    assert outcome['peak_rss_bytes']<512*2**20
    with (OUT/'ResourceStableGO-failure-assessment.json').open('x') as f:json.dump(outcome,f,indent=2,sort_keys=True);f.write('\n')
    print(json.dumps({k:outcome[k] for k in ('status','events','snapshots_offline_validated','collector_identity_equal','structural_projection_equal','raw_ps_process_sum_snapshot_bytes','exit','wall_seconds','peak_rss_bytes','swap')}))

if __name__=='__main__':main()
