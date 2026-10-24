#!/usr/bin/env python3
"""Offline source/input/decision audit; no host access or consumer launch."""
import hashlib
import importlib.util
import json
from pathlib import Path
import resource
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'evidence/resource-slab-20261024/threaded'

def load(name): return json.loads((OUT/name).read_text())
def sha(data): return hashlib.sha256(data).hexdigest()

def main():
    start=time.monotonic()
    spec=importlib.util.spec_from_file_location('candidate',Path(__file__).with_name('resource_slab_candidate.py'))
    candidate=importlib.util.module_from_spec(spec);spec.loader.exec_module(candidate)
    host=load('live-command.json')
    for name,digest in host['source_hashes'].items():
        data=Path(__file__).with_name(name).read_bytes()
        assert sha(data)==digest['sha256'] and len(data)==digest['size']
    before,after=load('snapshot-before.json'),load('snapshot-after.json')
    counts={}
    inputs={}
    for phase,snapshot in (('before',before),('after',after),('legacy',None)):
        attempts=[]
        for f in sorted(OUT.glob('reads-'+phase+'-*.json')):attempts.extend(json.loads(f.read_text()))
        latest={}
        errors=[]
        commands=[]
        for event in attempts:
            if 'content' in event:
                assert sha(event['content'].encode())==event['sha256']
                latest[event['path']]=event['sha256']
            elif 'command' in event:
                commands.append(dict(command=event['command'],exit=event.get('exit'),
                    stdout_sha256=sha((event.get('stdout') or '').encode()),
                    stderr_sha256=sha((event.get('stderr') or '').encode())))
            else:
                errors.append(event)
        if snapshot:
            assert latest==snapshot['raw_sha256']
            candidate.accounting(snapshot)
            assert all(e['errno']==95 and e['path'].endswith('/cgroup.procs') or
                       e['errno']==2 and e['path']=='/sys/fs/cgroup/cgroup.type' for e in errors)
        counts[phase]=dict(read_events=len(attempts),unique_successful_paths=len(latest),errors=errors,commands=commands)
        inputs[phase]=latest
    assert candidate.membership(before)==candidate.membership(after)
    decisions={}
    for size in (1,2,3,4,6,7,8):
        recorded=load(f'decision-{size}GiB.json')
        replay=candidate.propose(recorded['legacy'],before,after,size*candidate.GIB)
        assert replay==recorded
        old=recorded['legacy']
        decisions[str(size)]=dict(legacy_allowed=old['allowed'],candidate_allowed=recorded['allowed'],
            estimated_total_bytes=recorded['estimated_total_bytes'],
            physical_margin_bytes=min(before['meminfo']['MemTotal'],after['meminfo']['MemTotal'])-recorded['estimated_total_bytes'])
    d=load('decision-4GiB.json');a=d['before_accounting'];b=d['after_accounting']
    summary=dict(snapshot_nodes=len(before['rows']),snapshot_threads=sum(len(r['threads']) for r in before['rows']),
        actual_types={t:sum(r['type']==t for r in before['rows']) for t in sorted({r['type'] for r in before['rows']})},
        root_direct_processes=len(before['rows'][0]['procs']),
        empty_charged_groups=[r['path'] for r in before['rows'] if r['enabled'] and not r['populated'] and r['current']>0],
        root_residual_before=a['root_residual_bytes'],root_residual_after=b['root_residual_bytes'],
        bounded_reserved_bytes=a['bounded_reserved_bytes'],strict_limit_bytes=candidate.LIMIT,
        half_slab_envelope_bytes=sum(r['half_slab_credit'] for r in d['envelope']),
        inactive_file_envelope_bytes=sum(r['inactive_credit'] for r in d['envelope']),
        envelope_uncovered_reserve_bytes=sum(r['reserve'] for r in d['envelope']),decisions=decisions,
        coverage='complete observed hierarchy/thread/domain pair; not atomic or public-metadata completeness guarantee',
        adoption=False,print_axioms='N/A; formal budget ZERO')
    (OUT/'coverage-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    (OUT/'input-audit.json').write_text(json.dumps(dict(counts=counts,successful_input_hashes=inputs),indent=2)+'\n')
    usage=resource.getrusage(resource.RUSAGE_SELF)
    receipt=dict(command=['python3','-B','tools/resource-slab-20261024/audit_threaded.py'],exit=0,
        wall_seconds=time.monotonic()-start,peak_rss_bytes=usage.ru_maxrss,swaps=usage.ru_nswap,
        peak_scope='self; macOS ru_maxrss bytes',python=sys.version,
        source_version=subprocess.check_output(['git','rev-parse','HEAD'],text=True,cwd=ROOT).strip(),
        host_tested_source_version=host['source_version'],
        hashes={str(p.relative_to(ROOT)):sha(p.read_bytes()) for p in sorted(Path(__file__).parent.glob('*.py'))},
        print_axioms='N/A; formal budget ZERO',validation='offline exact decision replay, input hashes, membership/accounting; no additional host diagnostic')
    (OUT/'audit-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(summary))

if __name__=='__main__':main()
