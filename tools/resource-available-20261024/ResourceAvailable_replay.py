"""Original byte-identical gate replay with all external operations mocked."""
import contextlib
import datetime
import json
import os
from pathlib import Path
import runpy
import subprocess
from types import SimpleNamespace
from unittest.mock import patch
from ResourceAvailable_objects import ACTUAL, BASE, ROOT, sha

def replay(objects):
    report=objects.json(ACTUAL+'prospective-report-summary.json')
    export=objects.json(ACTUAL+'export-receipt.json')['host_files']
    events=[]
    for i in range(16):events.extend(objects.json(ACTUAL+f'prospective-ordered-{i:03}.json'))
    raw=(json.dumps(events,sort_keys=True,indent=2)+'\n').encode()
    assert dict(sha256=sha(raw),size=len(raw))=={k:export['prospective-ordered.json'][k] for k in ('sha256','size')}
    api=objects.run(BASE+'ResourceStat_go.py')
    objects.run(BASE+'baseline/reservation.py') # preload immutable nested source before mocks
    pos=0
    def take(kind,key,value):
        nonlocal pos
        e=events[pos];pos+=1
        assert e['kind']==kind and e[key]==value,(pos,e,kind,value)
        return e
    def error(e):
        cls=type(OSError(e['errno'],e['error']))
        return type('ResourceAvailableRecordedError',(cls,),{'__str__':lambda self:e['error']})(e['errno'],e['error'])
    def read(path,*a,**k):
        e=take('read','path',str(path))
        if e['errno']:raise error(e)
        assert sha(e['content'].encode())==e['sha256'] and len(e['content'].encode())==e['size']
        return e['content']
    @contextlib.contextmanager
    def scan(path):
        e=take('scandir','path',str(path))
        if 'error' in e:raise error(e)
        yield iter([SimpleNamespace(name=x['name'],path=x['path'],is_dir=lambda follow_symlinks=False,b=x['is_dir']:b) for x in e['entries']])
    def execute(args,*a,**k):
        e=take('command','command',args)
        if 'error' in e:
            if e.get('errno'):raise error(e)
            if e.get('exit') is not None:raise subprocess.CalledProcessError(e['exit'],args,output=e['stdout'],stderr=e['stderr'])
            raise subprocess.TimeoutExpired(args,k.get('timeout'),output=e.get('stdout'),stderr=e.get('stderr'))
        return subprocess.CompletedProcess(args,e['exit'],e['stdout'],e['stderr'])
    pid=int(next(e for e in events if e.get('path')=='/proc/self/stat' and not e.get('errno'))['content'].split(' ',1)[0])
    class Clock(datetime.datetime):
        @classmethod
        def now(cls,tz=None):return datetime.datetime.fromisoformat(report['original_legacy']['utc'])
    def readbytes(path):
        relative=str(path.relative_to(ROOT))
        assert relative in objects.cache,relative
        return objects.read(relative)
    with patch.object(Path,'read_bytes',readbytes),patch.object(datetime,'datetime',Clock),patch.object(Path,'read_text',read),patch.object(os,'scandir',scan),patch.object(os,'getpid',return_value=pid),patch.object(subprocess,'run',execute),patch.object(runpy,'run_path',objects.run):
        actual=api['read_only_admission'](phase='prospective',additional_bytes=4*2**30)
    assert pos==len(events)==15015
    assert actual['decision']==report['decision'] and actual['original_legacy']==report['original_legacy']
    for k in ('wall_seconds','peak_rss_kib','swaps'):actual[k]=report[k]
    raw=(json.dumps(actual,sort_keys=True,indent=2)+'\n').encode()
    assert dict(sha256=sha(raw),size=len(raw))=={k:export['prospective-report.json'][k] for k in ('sha256','size')}
    assert actual['decision']['allowed'] is False
    # Compare summaries while keeping the reconstructed raw evidence available to caller.
    for phase,s in actual['snapshots'].items():
        reduced={k:v for k,v in s.items() if k not in ('raw_inputs','read_attempts','self_read_attempts')}
        assert reduced==report['snapshots'][phase]
    return actual,dict(events=pos,original_decision=actual['decision'],original_hashes={k:export[k] for k in ('prospective-ordered.json','prospective-report.json')},gate_byte_identical=True)
