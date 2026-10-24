"""Nonmutating offline causal audit. Small summary default; no live authority."""
import contextlib
import hashlib
import json
import os
from pathlib import Path
import sys
from types import SimpleNamespace
from unittest.mock import patch
import ResourceAvailable_candidate as c
import ResourceAvailable_go as go
import ResourceAvailable_tests as tests
from ResourceAvailable_objects import Objects, REV, BASE, ACTUAL, ROOT, sha
from ResourceAvailable_replay import replay
ENTRY='ed3227f4dae529ed61d7f63c9dbd5adb8028e953'


def offline_guard(event,args):
    if event.startswith('socket.') or event in ('os.scandir','os.system','os.fork','os.posix_spawn'):
        raise RuntimeError('offline audit forbids '+event)
    if event=='subprocess.Popen' and args[1]!=['git','cat-file','--batch']:
        raise RuntimeError('offline audit forbids external command')
    if event=='open' and not isinstance(args[0],int):
        path,mode,flags=args[:3]
        if str(path).startswith(('/proc/','/sys/')):
            raise RuntimeError('offline audit forbids host reads')
        if (isinstance(mode,str) and any(x in mode for x in 'wax+')) or flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC):
            raise RuntimeError('nonmutating audit forbids writes')


def causal_scan(snapshot):
    """New observer consumes every original ordered read, including failures."""
    attempts=iter(snapshot['read_attempts'])
    def read(path,*a,**kw):
        e=next(attempts)
        assert e['path']==str(path),(e['path'],str(path))
        if e['errno']:
            cls=type(OSError(e['errno'],e['error']))
            error=type('ResourceAvailableRecordedError',(cls,),{'__str__':lambda self:e['error']})
            raise error(e['errno'],e['error'])
        assert sha(e['content'].encode())==e['sha256']
        return e['content']
    def scandir(path):
        children=[SimpleNamespace(path=r['path'],is_dir=lambda **kw:True) for r in snapshot['rows'] if r['parent']==str(path)]
        return contextlib.nullcontext(children)
    with patch.object(Path,'read_text',read),patch.object(os,'scandir',scandir):
        result=c.scan()
    assert next(attempts,None) is None
    for k in ('rows','meminfo','raw_sha256','raw_inputs','read_attempts'):
        assert result[k]==snapshot[k],k
    return dict(events=len(snapshot['read_attempts']),ordered_new_observer_replay=True,
        raw_paths=len(result['raw_inputs']))


def compact(d):
    return {k:v for k,v in d.items() if k in ('allowed','error','adjusted_available_bytes','required_bytes',
        'projected_reserved_bytes','min_mem_available_bytes','max_active_file_bytes',
        'max_kernel_withheld_bytes','max_root_residual_bytes','margin_bytes',
        'cap_ok','available_ok','legacy_nonreserve_gate_ok')}


def variant(old,q):
    # Counterfactual request projection only: retain all observed legacy errors,
    # visibility and nonreserve decisions rather than recomputing them away.
    if not old or 'bounded_reserved_bytes' not in old:
        return old
    result=dict(old)
    result['projected_reserved_bytes']=c.add((c.uint(old['bounded_reserved_bytes']),q))
    return result


def compare_pair(old,before,after):
    decisions={}
    for size in (1,2,3,4,6,7,8):
        q=size*c.GIB
        decisions[str(size)]=compact(go.evaluate(variant(old,q),before,after,q,phase='prospective'))
    return decisions


def main():
    sys.addaudithook(offline_guard)
    objects=Objects()
    try:
        focused=tests.run()
        measured,original=replay(objects)
        s=measured['snapshots'];old=measured['original_legacy']
        causal={p:causal_scan(s[p]) for p in ('before','after')}
        actual=compare_pair(old,s['before'],s['after'])
        assert actual['4']['adjusted_available_bytes']==39952494592,actual
        assert actual['4']['required_bytes']==37983617024,actual
        assert actual['4']['margin_bytes']==1968877568,actual
        assert actual['4']['allowed']
        # Full observed raw model remains available, summarized diagnostic anomalies.
        anomalies={}
        for p in ('before','after'):
            obs=c.observe(s[p])
            anomalies[p]=[d for d in obs['diagnostics'] if d['negative_components'] or d['type_lru_overlap'] or d['slab_exceeds_kernel'] or d['exclusive_current']<0]
        system=next(d for d in anomalies['before'] if d['path']=='/sys/fs/cgroup/system.slice')
        assert system['exclusive_stat']['anon']==-14086144
        user=next(d for d in anomalies['before'] if d['path']=='/sys/fs/cgroup/user.slice/user-1000.slice')
        assert user['positive_type_lru_sum']==32012546048
        reused={}
        # Assess old source and all immutable capture variants without new host reads.
        for prefix in ('evidence/resource-slab-20261024/',
                'evidence/resource-slab-20261024/failed-pids-assumption/',
                'evidence/resource-slab-20261024/threaded/',
                'evidence/resource-slab-20261024/go-api/'):
            snapshots={p:objects.json(prefix+'snapshot-'+p+'.json') for p in ('before','after')}
            legacy=objects.json(prefix+'legacy-snapshot.json')
            decisions=compare_pair(legacy,snapshots['before'],snapshots['after'])
            reused[prefix]=dict(label='historical counterfactual ONLY',decisions=decisions)
        # 14,587-event audit and old DENY results are reused, not rerun unchanged.
        assessments={}
        for path in ('evidence/resource-stat-20261024/ASSESSMENT.md',
                     'evidence/resource-stat-20261024/offline-summary.json',
                     'evidence/resource-stat-20261024/tests-receipt.json',
                     'evidence/resource-slab-20261024/go-api/coverage-summary.json',
                     'evidence/resource-slab-20261024/go-api/audit-receipt.json',
                     'evidence/resource-slab-20261024/immutable-source-assessment.json'):
            raw=objects.read(path)
            assessments[path]=dict(sha256=sha(raw),size=len(raw),status='REUSED')
        historical=objects.json('evidence/resource-stat-20261024/offline-summary.json')
        assert sum(historical['read_events'].values())==14587
        # Load merged hierarchy package from entry revision with independent sealed namespace.
        merged=Objects()
        try:
            # Objects stream is private; revision pin is changed only for this instance.
            merged.revision=ENTRY
            for path in ('evidence/resource-hierarchy-20261024/summary.json',
                         'evidence/resource-hierarchy-20261024/SOURCE-ASSESSMENT.md',
                         'evidence/resource-hierarchy-20261024/audit-final-receipt.json',
                         'evidence/resource-actual-20261024/REPORT.md'):
                merged.read(path)
            summary=merged.json('evidence/resource-hierarchy-20261024/summary.json')
            assert all(not d['allowed'] for d in summary['counterfactual_reused_pair_only'].values())
            hierarchy_reused=dict(revision=ENTRY,pins=merged.pins,old_all_deny=True,
                status='REUSED; unchanged hierarchy suite/audit not rerun')
        finally:merged.close()
        output=dict(schema='ResourceAvailable-offline-audit-v1',status='PASS',adopted=False,
            live_boundary='DISABLED',current_headroom='UNKNOWN',new_host_reads=0,
            print_axioms='N/A; formal budget ZERO',focused_validation=focused,
            original_replay=original,new_observer_causal_scan=causal,
            actual_pair_counterfactual_only=actual,diagnostic_anomalies=anomalies,
            reused_capture_counterfactuals=reused,reused_assessments=assessments,
            reused_14587_events=True,reused_hierarchy=hierarchy_reused,
            immutable_revision=REV,input_and_dependency_hashes=objects.pins,
            limits='Recorded estimate only; no atomicity, reclaim, future guarantee, binary identity, adoption or real GO/consumer')
        raw=json.dumps(output,sort_keys=True,indent=2)+'\n'
        assert len(raw.encode())<5_000_000
        if '--details' in sys.argv:
            print(raw,end='')
        else:
            print(json.dumps(dict(schema=output['schema'],status=output['status'],
                focused_validation=focused,events=original['events'],
                original_gate_byte_identical=original['gate_byte_identical'],
                original_hashes=original['original_hashes'],
                actual_pair_counterfactual_only=actual,
                reused_capture_counterfactuals=reused,
                new_observer_causal_scan=causal,new_host_reads=0,
                live_boundary='DISABLED',current_headroom='UNKNOWN',
                adopted=False,print_axioms=output['print_axioms']),sort_keys=True,indent=2))
    finally:objects.close()

if __name__=='__main__':main()
