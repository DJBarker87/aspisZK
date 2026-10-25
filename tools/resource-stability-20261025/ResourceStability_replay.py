"""Exact original v2 causal replay, adapted from immutable ResourceAdmit_audit.

All external reads/commands during the original API call consume ordered
captured events. No old evaluator or scanner globals are changed.
"""
import contextlib
import hashlib
import json
import os
from pathlib import Path
import subprocess
from types import SimpleNamespace
from unittest.mock import patch
from ResourceStability_sources import blob, digest, original_v2_adapter

PREFIX='evidence/resource-admit-20261024/v2/'


def data(name,prefix=PREFIX):return json.loads(blob(prefix+name))


def replay_v2():
    adapter=original_v2_adapter()
    # Verify API and dependency source bytes against the original launch manifest.
    manifest=data('manifest.json')
    import ResourceStability_sources as sources
    reviewed={}
    for key,(revision,path) in {
        'candidate':(sources.AVAILABLE,'tools/resource-available-20261024/ResourceAvailable_candidate.py'),
        'go':(sources.AVAILABLE,'tools/resource-available-20261024/ResourceAvailable_go.py'),
        'identity':(sources.ACTUAL,'tools/resource-stat-20261024/ResourceStat_go.py'),
        'inventory':(sources.ACTUAL,'tools/resource-stat-20261024/baseline/reservation_base.py'),
        'fixtures':(sources.AVAILABLE,'tools/resource-available-20261024/ResourceAvailable_tests.py'),
    }.items():
        raw=blob(path,revision)
        reviewed[key]=dict(revision=revision,path=path,source=raw.decode(),**digest(raw))
    for name,pin in manifest['files'].items():
        raw=(json.dumps(reviewed,sort_keys=True,indent=2)+'\n').encode() if name=='ResourceAdmit_reviewed.json' else blob('tools/resource-admit-20261024/'+name)
        assert digest(raw)==pin,('original source drift',name)
    export=data('export-receipt.json')
    events=[]
    for index in range(15):
        name=f'prospective-ordered-{index:03}.json'
        raw=blob(PREFIX+name)
        # Shard pins are sealed by the original audit receipt, not export.
        receipt=data('actual-audit-v2-receipt.json') if index==0 else receipt
        assert digest(raw)==receipt['inputs'][name]
        events.extend(json.loads(raw))
    ordered=(json.dumps(events,sort_keys=True,indent=2)+'\n').encode()
    input_pin=digest(ordered)
    assert input_pin=={k:export['host_files']['prospective-ordered.json'][k] for k in ('sha256','size')}
    assert input_pin=={k:data('prospective-ordered.json.hash.json')[k] for k in ('sha256','size')}
    del ordered
    raw=blob(PREFIX+'prospective-report-summary.json')
    assert digest(raw)==receipt['inputs']['prospective-report-summary.json']
    report=json.loads(raw)
    position=0
    def take(kind,key,value):
        nonlocal position
        assert position<len(events),('extra input',kind,value)
        event=events[position];position+=1
        assert event['kind']==kind and event[key]==value,(position,event,kind,value)
        return event
    def raw_error(e):
        kind=type(OSError(e['errno'],e['error']))
        return type(kind.__name__,(kind,),{'__str__':lambda self:e['error']})(e['errno'],e['error'])
    def read(path,*a,**k):
        e=take('read','path',str(path))
        if e['errno']:raise raw_error(e)
        assert digest(e['content'].encode())=={key:e[key] for key in ('sha256','size')}
        return e['content']
    @contextlib.contextmanager
    def scan(path):
        e=take('scandir','path',str(path))
        if 'error' in e:raise raw_error(e)
        yield iter([SimpleNamespace(name=x['name'],path=x['path'],
            is_dir=lambda follow_symlinks=False,b=x['is_dir']:b) for x in e['entries']])
    def execute(args,*a,**k):
        e=take('command','command',args)
        if 'error' in e:
            if e.get('errno'):raise raw_error(e)
            if e.get('exit') is not None:raise subprocess.CalledProcessError(e['exit'],args,output=e['stdout'],stderr=e['stderr'])
            raise subprocess.TimeoutExpired(args,k.get('timeout'),output=e.get('stdout'),stderr=e.get('stderr'))
        return subprocess.CompletedProcess(args,e['exit'],e['stdout'],e['stderr'])
    assert type(report['collector_pid']) is int and report['collector_pid']>0
    with patch.object(Path,'read_text',read),patch.object(os,'scandir',scan),\
            patch.object(os,'getpid',return_value=report['collector_pid']),\
            patch.object(subprocess,'run',execute):
        actual=adapter.read_only_admission(phase='prospective')
    assert position==len(events)==14926
    assert actual['decision']==report['decision']
    assert actual['original_legacy']==report['original_legacy']
    rebuilt=(json.dumps(actual,sort_keys=True,indent=2)+'\n').encode()
    report_pin=digest(rebuilt)
    assert report_pin=={k:export['host_files']['prospective-report.json'][k] for k in ('sha256','size')}
    assert report_pin=={k:data('prospective-report.json.hash.json')[k] for k in ('sha256','size')}
    del rebuilt,events
    for label,snapshot in actual['snapshots'].items():
        # Summary omits only duplicated raw evidence; original remains intact.
        projected={k:v for k,v in snapshot.items() if k not in ('raw_inputs','read_attempts','self_read_attempts')}
        assert projected==report['snapshots'][label]
    assert actual['decision']['allowed'] is False
    assert actual['decision']['error']=='ValueError: hierarchy/membership/control race'
    assert data('run-exit.json')['terminal']=='PROSPECTIVE_DENY'
    # Immutable tree has no actual phase, scope argv or marker in this v2 packet.
    paths=subprocess.check_output(['git','ls-tree','-r','--name-only',sources.ENTRY,PREFIX],cwd=sources.ROOT,text=True).splitlines()
    for name in ('scope-argv.json','marker.json','inside-scope-report.json','go-controls-before.json'):
        assert PREFIX+name not in paths
    return actual,dict(status='PASS: exact original DENY replay only',events=position,
        input=input_pin,report=report_pin,original_error=actual['decision']['error'],
        original_allowed=False,actual_scope=False,GO=False,marker=False,
        original_api='ResourceAdmit20261025-v2',unchanged_original_sources=True)
