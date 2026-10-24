#!/usr/bin/env python3
"""Offline full input replay; no remote access, build or consumer."""
import contextlib
import hashlib
import importlib.util
import json
from pathlib import Path
import resource
import subprocess
import sys
import time
from unittest.mock import patch
import go_api as go

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'evidence/resource-slab-20261024/go-api'

def sha(data): return hashlib.sha256(data).hexdigest()
def load(name): return json.loads((OUT/name).read_text())
def save(name,data):
    raw=(json.dumps(data,indent=2)+'\n').encode()
    if len(raw)>5_000_000:raw=(json.dumps(dict(omitted=True,sha256=sha(raw),size=len(raw)))+'\n').encode()
    (OUT/name).write_bytes(raw)


def replay_scan(snapshot,attempts):
    class Entry:
        def __init__(self,path):self.path=path
        def is_dir(self,**kw):return True
    iterator=iter(attempts)
    def read(path,*args,**kwargs):
        event=next(iterator)
        assert event['path']==str(path),(event['path'],str(path))
        if event['errno']:raise OSError(event['errno'],event.get('error','recorded error'))
        return event['content']
    def scandir(path):
        return contextlib.nullcontext([Entry(r['path']) for r in snapshot['rows'] if r['parent']==str(path)])
    with patch.object(Path,'read_text',read),patch.object(go.base['os'],'scandir',scandir):
        result=go.base['scan']()
    assert next(iterator,None) is None
    for key in ('rows','meminfo','raw_sha256'):assert result[key]==snapshot[key],key
    return result


def main():
    start=time.monotonic()
    host=load('live-command.json')
    for name,digest in host['source_hashes'].items():
        data=Path(__file__).with_name(name).read_bytes()
        assert sha(data)==digest['sha256'] and len(data)==digest['size']
    immutable={}
    for name in ('reservation.py','reservation_base.py'):
        data=subprocess.check_output(['git','show','f033f68bf7:tools/prover-rw-20261023/resume-roles/'+name],cwd=ROOT)
        assert data==Path(__file__).with_name(name).read_bytes()
        immutable[name]=dict(sha256=sha(data),size=len(data),assessment='byte-identical historical source; reused assessment, not new ELF gate')
    before,after=load('snapshot-before.json'),load('snapshot-after.json')
    counts={}
    input_hashes={}
    accounting_results={}
    accounting_errors={}
    for phase,snapshot in (('before',before),('after',after),('legacy',None)):
        attempts=[]
        for f in sorted(OUT.glob('reads-'+phase+'-*.json')):attempts+=json.loads(f.read_text())
        latest={};errors=[];commands=[]
        for event in attempts:
            if 'content' in event:
                assert sha(event['content'].encode())==event['sha256']
                latest[event['path']]=event['sha256']
            elif 'command' in event:
                commands.append(dict(command=event['command'],exit=event.get('exit'),stdout_sha256=sha((event.get('stdout') or '').encode()),stderr_sha256=sha((event.get('stderr') or '').encode())))
            else:errors.append(event)
        if snapshot:
            assert latest==snapshot['raw_sha256']
            raw={}
            for f in sorted(OUT.glob('inputs-'+phase+'-*.json')):
                for path,value in json.loads(f.read_text())['inputs'].items():
                    assert path not in raw
                    raw[path]=value
            assert {k:sha(v.encode()) for k,v in raw.items()}==latest
            replay_scan(snapshot,attempts)
            obs=snapshot['self_observation']
            events=snapshot['self_read_attempts']
            for event in events:assert sha(event['content'].encode())==event['sha256']
            iterator=iter(events)
            def read_self(path,*args,**kwargs):
                event=next(iterator);assert str(path)==event['path'];return event['content']
            with patch.object(Path,'read_text',read_self),patch.object(go.os,'getpid',return_value=obs['pid']):
                first,second=go.self_observation(),go.self_observation()
            assert next(iterator,None) is None
            stable=lambda v:{k:x for k,x in v.items() if k!='reads'}
            assert stable(first)==stable(second)==stable(obs)
            assert first==obs
            row=next(r for r in snapshot['rows'] if r['path']==obs['path'])
            assert obs['pid'] in row['procs']
            assert dict(tid=obs['pid'],tgid=obs['pid'],starttime=obs['starttime']) in row['identities']
            try: accounting_results[phase]=go.accounting(snapshot)
            except (ValueError,KeyError,TypeError) as exc: accounting_errors[phase]=str(exc)
            assert all(e['errno']==95 and e['path'].endswith('/cgroup.procs') or e['errno']==2 and e['path']=='/sys/fs/cgroup/cgroup.type' for e in errors)
        counts[phase]=dict(read_events=len(attempts),unique_successful_paths=len(latest),errors=errors,commands=commands)
        input_hashes[phase]=latest
    assert go.membership(before)==go.membership(after)
    original=load('legacy-snapshot.json')
    decisions={}
    for size in (1,2,3,4,6,7,8):
        recorded=load(f'decision-{size}GiB.json')
        assert recorded==go.evaluate(go.legacy_request(original,size*go.GIB),before,after,size*go.GIB,phase='prospective')
        decisions[str(size)]=dict(allowed=recorded['allowed'],legacy_allowed=recorded['legacy']['allowed'],error=recorded.get('error'),estimated_total_bytes=recorded.get('estimated_total_bytes'),physical_margin_bytes=(min(before['meminfo']['MemTotal'],after['meminfo']['MemTotal'])-recorded['estimated_total_bytes']) if 'estimated_total_bytes' in recorded else None)
    live=load('live-summary.json');recorded=live['actual_collector_go']
    assert recorded==go.evaluate(go.legacy_request(original,0),before,after,0,phase='inside-scope',expected=recorded['expected_limits'])
    assert not recorded['allowed'] # expected physical observation outside a scope
    defects={}
    for phase,snapshot in (('before',before),('after',after)):
        bad=[]
        for row in snapshot['rows']:
            if not row['enabled']:continue
            children=[r for r in snapshot['rows'] if r['parent']==row['path'] and r['enabled']]
            current=row['current']-sum(c['current'] for c in children)
            ex={k:row['stat'][k]-sum(c['stat'][k] for c in children) for k in go.base['REQUIRED']}
            disjoint=sum(ex[k] for k in ('inactive_file','active_file','anon','kernel'))
            if current<0 or any(v<0 or v>current for v in ex.values()) or disjoint>current or ex['slab_reclaimable']+ex['slab_unreclaimable']>ex['kernel']:
                bad.append(dict(path=row['path'],exclusive_current=current,exclusive_stat=ex,disjoint_total=disjoint,excess_over_current=disjoint-current))
        defects[phase]=bad
    # Diagnostic facts remain recorded even when accounting fails. They are
    # never substituted into the candidate estimate to manufacture admission.
    root_residual=[]
    for snapshot in (before,after):
        root=snapshot['rows'][0]
        top=sum(r['current'] for r in snapshot['rows'] if r['enabled'] and r['owner']==root['path'])
        root_residual.append(snapshot['meminfo']['MemTotal']-snapshot['meminfo']['MemFree']-top)
    self_row=next(r for r in before['rows'] if r['path']==before['self_observation']['path'])
    summary=dict(api_version=go.API_VERSION,
        actual_collector_observed_limits={k:self_row.get(k) for k in ('high','cap','swap_max','tasks_max','swap_current','enabled','populated')},
        actual_collector_expected_limits=recorded['expected_limits'],immutable_source_assessment=immutable,
        snapshot_nodes=[len(s['rows']) for s in (before,after)],snapshot_threads=[sum(len(r['threads']) for r in s['rows']) for s in (before,after)],
        actual_types={t:sum(r['type']==t for r in before['rows']) for t in sorted({r['type'] for r in before['rows']})},
        self_observations=[{k:v for k,v in s['self_observation'].items() if k!='reads'} for s in (before,after)],
        root_direct_processes=len(before['rows'][0]['procs']),
        empty_charged_groups=[r['path'] for r in before['rows'] if r['enabled'] and not r['populated'] and r['current']>0],
        root_residual_bytes=root_residual,
        bounded_reserved_bytes=original['bounded_reserved_bytes'],strict_limit_bytes=go.LIMIT,
        mem_total_bytes=min(before['meminfo']['MemTotal'],after['meminfo']['MemTotal']),mem_available_bytes=min(before['meminfo']['MemAvailable'],after['meminfo']['MemAvailable']),
        accounting_errors=accounting_errors, inconsistent_exclusive_cells=defects,
        current_prospective_headroom='unknown; inconsistent snapshots deny all sizes; no envelope/credit/total claimed',
        os_control_bytes=7*go.GIB,decisions=decisions,actual_collector_go=dict(allowed=recorded['allowed'],error=recorded.get('error')),
        coverage='complete observed hierarchy/membership pair; ordered read replay including self; accounting consistency FAILS; point-in-time only',
        half_slab='estimate only; no active-file or root-residual credit',adopted=False,print_axioms='N/A; formal budget ZERO')
    save('coverage-summary.json',summary)
    save('input-audit.json',dict(counts=counts,input_hashes=input_hashes,full_scanner_replay=True,self_replay=True))
    usage=resource.getrusage(resource.RUSAGE_SELF)
    save('audit-receipt.json',dict(command=['python3','-B','tools/resource-slab-20261024/audit_go.py'],exit=0,
        wall_seconds=time.monotonic()-start,peak_rss_bytes=usage.ru_maxrss,swap=usage.ru_nswap,platform='macOS self ru_maxrss bytes; child/aggregate N/A',
        source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),host_source_revision=host['source_version'],
        source_dependency_hashes={str(p.relative_to(ROOT)):dict(sha256=sha(p.read_bytes()),size=p.stat().st_size) for p in sorted(Path(__file__).parent.glob('*.py'))},
        interpreter=sys.version,input_manifest_sha256=sha((OUT/'input-audit.json').read_bytes()),print_axioms='N/A; formal budget ZERO'))
    print(json.dumps(summary))

if __name__=='__main__':main()
