"""Nonmutating offline replay of every observed input and admission decision.

Run from any cwd with python3 -B <this file>. Does not use SSH or write files.
"""
import contextlib
import datetime
import hashlib
import json
import os
from pathlib import Path
import runpy
import subprocess
import sys
from types import SimpleNamespace
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'evidence/resource-admit-20261024'
import ResourceAdmit_adapter as adapter
import ResourceAdmit_sources as sources


def load(name):return json.loads((OUT/name).read_text())


def replay(phase):
    source=OUT/(phase+'-ordered.json')
    if source.exists():events=json.loads(source.read_text())
    else:
        events=[]
        for shard in sorted(OUT.glob(phase+'-ordered-*.json')):events.extend(json.loads(shard.read_text()))
    ordered_pin=load('export-receipt.json')['host_files'][phase+'-ordered.json']
    ordered_raw=(json.dumps(events,sort_keys=True,indent=2)+'\n').encode()
    assert len(ordered_raw)==ordered_pin['size'] and hashlib.sha256(ordered_raw).hexdigest()==ordered_pin['sha256']
    summary=OUT/(phase+'-report.json')
    report=json.loads(summary.read_text()) if summary.exists() else load(phase+'-report-summary.json')
    api=adapter.__dict__
    # Freeze API clock/RSS fields only after comparing every decision/input.
    position=0
    def take(kind,key,value):
        nonlocal position
        assert position<len(events),('extra replay input',kind,value)
        event=events[position];position+=1
        assert event['kind']==kind and event[key]==value,(position,event,kind,value)
        return event
    def raw_error(e):
        kind=type(OSError(e['errno'],e['error']))
        return type('RecordedError',(kind,),{'__str__':lambda self:e['error']})(e['errno'],e['error'])
    def read(path,*a,**k):
        e=take('read','path',str(path))
        if e['errno']:raise raw_error(e)
        assert hashlib.sha256(e['content'].encode()).hexdigest()==e['sha256']
        assert len(e['content'].encode())==e['size']
        return e['content']
    @contextlib.contextmanager
    def scan(path):
        e=take('scandir','path',str(path))
        if 'error' in e:raise raw_error(e)
        yield iter([SimpleNamespace(name=x['name'],path=x['path'],is_dir=lambda follow_symlinks=False,b=x['is_dir']:b) for x in e['entries']])
    def execute(args,*a,**k):
        e=take('command','command',args)
        if 'error' in e:
            if e.get('errno'):raise raw_error(e)
            if e.get('exit') is not None:raise subprocess.CalledProcessError(e['exit'],args,output=e['stdout'],stderr=e['stderr'])
            raise subprocess.TimeoutExpired(args,k.get('timeout'),output=e.get('stdout'),stderr=e.get('stderr'))
        return subprocess.CompletedProcess(args,e['exit'],e['stdout'],e['stderr'])
    first=next(e for e in events if e.get('path')=='/proc/self/stat' and not e.get('errno'))
    pid=int(first['content'].split(' ',1)[0])
    with patch.object(Path,'read_text',read),patch.object(os,'scandir',scan),patch.object(os,'getpid',return_value=pid),patch.object(subprocess,'run',execute):
        actual=api['read_only_admission'](phase=phase)
    assert position==len(events),('unconsumed inputs',position,len(events))
    assert actual['decision']==report['decision'],('decision differs',actual['decision'],report['decision'])
    assert actual['original_legacy']==report['original_legacy']
    # Reconstruct ALL original report bytes; recorded measurement scalars are
    # retained rather than represented as measurements of this offline replay.
    rebuilt=(json.dumps(actual,sort_keys=True,indent=2)+'\n').encode()
    original_pin=load('export-receipt.json')['host_files'][phase+'-report.json']
    assert len(rebuilt)==original_pin['size'] and hashlib.sha256(rebuilt).hexdigest()==original_pin['sha256']
    # Summary excludes only exact duplicates of separately retained raw reads.
    for value in (actual,report):
        for snapshot in value['snapshots'].values():
            if snapshot:
                for key in ('raw_inputs','read_attempts','self_read_attempts'):snapshot.pop(key,None)
    assert actual['snapshots']==report['snapshots']
    return dict(events=position,allowed=actual['decision']['allowed'],error=actual['decision'].get('error'),
                collection_failures=actual['decision'].get('collection_failures'))


def main():
    manifest=load('manifest.json')
    for name,pin in manifest['files'].items():
        p=Path(__file__).with_name(name)
        raw=(json.dumps(sources.bundle(),sort_keys=True,indent=2)+chr(10)).encode() if name=='ResourceAdmit_reviewed.json' else p.read_bytes()
        assert pin==dict(sha256=hashlib.sha256(raw).hexdigest(),size=len(raw))
    export=load('export-receipt.json')
    for name,pin in export['host_files'].items():
        p=OUT/name
        if p.exists():
            raw=p.read_bytes();assert len(raw)==pin['size'] and hashlib.sha256(raw).hexdigest()==pin['sha256']
        else:assert load(name+'.hash.json')==pin
    for name in ('run-pre-pins.json','run-post-pins.json','go-pre-pins.json','go-pins.json','go-post-pins.json'):
        if (OUT/name).exists():
            observed=load(name)
            for key in ('files','runtime','env'):assert observed[key]==manifest[key]
    phases={}
    for phase in ('prospective','inside-scope'):
        if (OUT/(phase+'-report.json')).exists() or (OUT/(phase+'-report-summary.json')).exists():phases[phase]=replay(phase)
    assert 'prospective' in phases
    if not phases['prospective']['allowed']:
        assert 'inside-scope' not in phases
        assert not (OUT/'scope-argv.json').exists()
        assert not (OUT/'marker.json').exists()
        assert load('run-exit.json')['terminal']=='PROSPECTIVE_DENY'
    if 'inside-scope' in phases and not phases['inside-scope']['allowed']:assert not (OUT/'marker.json').exists()
    print(json.dumps(dict(status='PASS',phases=phases,print_axioms='N/A'),sort_keys=True))

if __name__=='__main__':main()
