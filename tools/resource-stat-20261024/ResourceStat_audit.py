"""Nonmutating offline review of immutable ordered observations. No host calls.

Outputs only to assigned ResourceStat evidence. Git objects are streamed, never
populated as a historical checkout. Prior audits are loaded, never main() run.
"""
import contextlib
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
from unittest.mock import patch
import ResourceStat_go as go

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
OUT=ROOT/'evidence/resource-stat-20261024'
REV='25b0b9df48'
PREFIX='evidence/resource-slab-20261024/go-api/'

def sha(data):return hashlib.sha256(data).hexdigest()
def save(name,obj):
    raw=(json.dumps(obj,indent=2)+'\n').encode()
    if len(raw)>5_000_000:raw=(json.dumps(dict(sha256=sha(raw),size=len(raw),omitted=True))+'\n').encode()
    (OUT/name).write_bytes(raw)

class Objects:
    def __init__(self):
        self.proc=subprocess.Popen(['git','cat-file','--batch'],cwd=ROOT,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
        self.hashes={}
    def read(self,path):
        self.proc.stdin.write((REV+':'+path+'\n').encode());self.proc.stdin.flush()
        header=self.proc.stdout.readline().decode().split();assert len(header)==3,header
        data=self.proc.stdout.read(int(header[2]));assert self.proc.stdout.read(1)==b'\n'
        self.hashes[path]=dict(git_blob=header[0],sha256=sha(data),size=len(data))
        return data
    def load(self,name):return json.loads(self.read(PREFIX+name))
    def close(self):
        self.proc.stdin.close();assert self.proc.wait()==0


def main():
    objects=Objects()
    names=subprocess.check_output(['git','ls-tree','-r','--name-only',REV,PREFIX],cwd=ROOT,text=True).splitlines()
    baseline=HERE/'baseline'
    spec=importlib.util.spec_from_file_location('ResourceStat_historical_audit',baseline/'audit_go.py')
    historical=importlib.util.module_from_spec(spec)
    # audit_go imports old name; bind it explicitly to the candidate scan API.
    with patch.dict(sys.modules,go_api=go):spec.loader.exec_module(historical)
    historical.go=go
    snapshots={phase:objects.load('snapshot-'+phase+'.json') for phase in ('before','after')}
    old=objects.load('legacy-snapshot.json')
    live=objects.load('live-summary.json')
    command=objects.load('live-command.json')
    for name,record in command['source_hashes'].items():
        data=(baseline/name).read_bytes()
        assert sha(data)==record['sha256'] and len(data)==record['size']
    count={};orders={};legacy_events=[]
    for phase in ('before','after','legacy'):
        events=[]
        for path in sorted(p for p in names if p.startswith(PREFIX+'reads-'+phase+'-')):
            events+=json.loads(objects.read(path))
        for e in events:
            if 'content' in e:assert sha(e['content'].encode())==e['sha256']
        count[phase]=len(events)
        if phase=='legacy':legacy_events=events;continue
        s=snapshots[phase]
        replayed=historical.replay_scan(s,events)
        assert replayed['raw_sha256']==s['raw_sha256']
        raw={}
        for path in sorted(p for p in names if p.startswith(PREFIX+'inputs-'+phase+'-')):
            for key,value in json.loads(objects.read(path))['inputs'].items():
                assert key not in raw;raw[key]=value
        assert {k:sha(v.encode()) for k,v in raw.items()}==s['raw_sha256']
        obs=s['self_observation'];selfevents=s['self_read_attempts'];it=iter(selfevents)
        for e in selfevents:assert sha(e['content'].encode())==e['sha256']
        def selfread(path,*args,**kwargs):
            e=next(it);assert str(path)==e['path'];return e['content']
        with patch.object(Path,'read_text',selfread),patch.object(go.os,'getpid',return_value=obs['pid']):
            first,second=go.self_observation(),go.self_observation()
        stable=lambda r:{k:v for k,v in r.items() if k!='reads'}
        assert next(it,None) is None
        assert first==obs and stable(first)==stable(second)
        row=next(r for r in s['rows'] if r['path']==obs['path'])
        assert dict(tid=obs['pid'],tgid=obs['pid'],starttime=obs['starttime']) in row['identities']
        target='/sys/fs/cgroup/system.slice/hausklar-fitness-worker.service'
        orders[phase]=[dict(index=i,**e) for i,e in enumerate(events) if e.get('path') in (target+'/memory.current',target+'/memory.stat')]
        assert orders[phase][0]['path'].endswith('/memory.current')
        assert orders[phase][1]['path'].endswith('/memory.stat')
    # Replay legacy reads AND ps/systemctl/docker commands in exact order.
    import runpy
    legacy=runpy.run_path(str(baseline/'reservation.py'))
    events=iter(legacy_events)
    def readlegacy(path,*args,**kwargs):
        e=next(events);assert e['path']==str(path)
        if e['errno']:raise OSError(e['errno'],e.get('error','recorded'))
        return e['content']
    def runlegacy(args,*pos,**kwargs):
        e=next(events);assert args==e['command']
        if e['exit']:raise subprocess.CalledProcessError(e['exit'],args,e.get('stdout'),e.get('stderr'))
        return subprocess.CompletedProcess(args,e['exit'],e.get('stdout'),e.get('stderr'))
    class Entry:
        def __init__(self,path):self.path=path
        def is_dir(self,**kw):return True
    def scandir(path):
        return contextlib.nullcontext([Entry(r['path']) for r in old['cgroups'] if str(Path(r['path']).parent)==str(path) and r['path']!=str(path)])
    with patch.object(Path,'read_text',readlegacy),patch.object(subprocess,'run',runlegacy),patch.object(go.os,'scandir',scandir):
        replay=legacy['admission'](requested=old['requested_bytes'])
    assert next(events,None) is None
    assert {k:v for k,v in replay.items() if k!='utc'}=={k:v for k,v in old.items() if k!='utc'}
    assert go.membership(snapshots['before'])==go.membership(snapshots['after'])
    # Historical decisions continue to replay as denials, never rewritten.
    oldgo=runpy.run_path(str(baseline/'go_api.py'))
    decisions={}
    for size in (1,2,3,4,6,7,8):
        q=size*go.GIB;lg=go.legacy_request(old,q)
        original=objects.load(f'decision-{size}GiB.json')
        assert oldgo['evaluate'](lg,snapshots['before'],snapshots['after'],q,phase='prospective')==original
        d=go.evaluate(lg,snapshots['before'],snapshots['after'],q,phase='prospective')
        assert 'error' not in d,d
        decisions[str(size)]=d
    before,after=snapshots['before'],snapshots['after']
    target='/sys/fs/cgroup/system.slice/hausklar-fitness-worker.service'
    for a,b in ((before,after),(after,before)):
        d=go.evaluate(go.legacy_request(old,go.GIB),a,b,go.GIB,phase='prospective')
        cell=next(r for r in d['envelope'] if r['path']==target)
        selfafter=next(r for r in go.accounting(after)['exclusive'] if r['path']==target)
        assert selfafter['exclusive_current']==12107776
        assert selfafter['disjoint_total']==12111872 and selfafter['excess_over_current']==4096
        assert cell['fallback'] and cell['reserve']==max(12111872,next(r for r in go.accounting(before)['exclusive'] if r['path']==target)['conservative_charge'])
        assert cell['inactive_credit']==cell['half_slab_credit']==0
    expected=live['actual_collector_go']['expected_limits']
    actual=go.evaluate(go.legacy_request(old,0),before,after,0,phase='inside-scope',expected=expected)
    assert not actual['allowed'] and 'scope controls differ' in actual['error']
    assert oldgo['evaluate'](oldgo['legacy_request'](old,0),before,after,0,phase='inside-scope',expected=expected)==live['actual_collector_go']
    # Pair padding must not consume root residual or grant any cell credit.
    base=decisions['1'];a,b=base['before_accounting'],base['after_accounting']
    assert [a['root_residual_bytes'],b['root_residual_bytes']]==[2247208960,2240557056]
    fallback=[r for r in base['envelope'] if r['fallback']]
    save('recorded-orders.json',orders)
    save('recorded-decisions.json',dict(schema=go.API_VERSION,measurement='reused historical pair, not current host authority',prospective=decisions,actual_collector_go=actual))
    save('offline-summary.json',dict(schema=go.API_VERSION,revision=REV,adopted=False,new_host_captures=0,
        read_events=count,legacy_ordered_replay=True,scanner_ordered_replay=True,self_ordered_replay=True,
        input_shards_hash_verified=True,nodes=[len(s['rows']) for s in (before,after)],
        tids=[sum(len(r['threads']) for r in s['rows']) for s in (before,after)],
        fallback_cells=fallback,root_residual_bytes=[a['root_residual_bytes'],b['root_residual_bytes']],
        bounded_reserved_bytes=a['bounded_reserved_bytes'],os_control_bytes=7*go.GIB,
        decisions={k:dict(allowed=d['allowed'],estimate=d['estimated_total_bytes'],margin=min(before['meminfo']['MemTotal'],after['meminfo']['MemTotal'])-d['estimated_total_bytes']) for k,d in decisions.items()},
        actual_go=actual['error'],print_axioms='N/A; ZERO formal work',
        limitation='point-in-time estimate on historical inputs, no real capped consumer or safety guarantee'))
    objects.close();save('input-manifest.json',dict(revision=REV,files=objects.hashes))
    print(json.dumps(dict(result='PASS',reads=count,fallback_cells=len(fallback),actual_go=False)))

if __name__=='__main__':main()
