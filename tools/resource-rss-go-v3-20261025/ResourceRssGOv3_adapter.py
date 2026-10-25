"""Job-only metadata live boundary. Reviewed ResourceStability policy used for one explicitly allocated epoch only."""
import json
import os
from pathlib import Path
import subprocess
from ResourceRssGOv3_sources import load

c, go, identity, inventory, policy = load()
EXPECTED=dict(high=3*c.GIB,cap=4*c.GIB,swap_max=0,tasks_max=64)
UNIT='resource-rss-go-v3-20261025'
COMMANDS=[['ps','-e','-o','pid,ppid,rss,comm,cgroup'],
          ['systemctl','list-units','--type=service','--state=running','--no-pager','--no-legend'],
          ['docker','ps','-q']]

def visibility(requested):
    """Legacy independent frontier and commands, without obsolete accounting."""
    rows=inventory['inventory'](Path('/sys/fs/cgroup'))
    reserved=c.add(r['charged_bytes'] for r in rows)
    def run(args):
        return subprocess.run(args,check=True,text=True,stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE,timeout=15).stdout
    processes=run(COMMANDS[0]);services=run(COMMANDS[1]);ids=run(COMMANDS[2]).split()
    if len(ids)!=len(set(ids)) or any(not x.isascii() or any(ch not in '0123456789abcdef' for ch in x) for x in ids):
        raise ValueError('invalid/duplicate Docker identity')
    containers=[]
    for cid in ids:
        state=json.loads(run(['docker','inspect','--format','{{json .State}}',cid]))
        config=json.loads(run(['docker','inspect','--format','{{json .HostConfig}}',cid]))
        if not isinstance(state,dict) or not isinstance(config,dict):raise ValueError('invalid Docker metadata')
        if type(state.get('Running')) is not bool or state['Running'] is not True or not c.uint(state['Pid']):
            raise ValueError('invalid/racing Docker process state')
        for key in ('Memory','MemorySwap'):
            value=config[key]
            if type(value) is not int or value < (-1 if key=='MemorySwap' else 0) or value>c.U64:
                raise ValueError('invalid Docker resource metadata')
        containers.append(dict(state,id=cid,host_config=config))
    lines=processes.splitlines()
    if not lines or lines[0].split() != ['PID','PPID','RSS','COMMAND','CGROUP']:
        raise ValueError('malformed process visibility header')
    pids=set()
    for line in lines[1:]:
        words=line.split(None,3)
        if len(words)!=4:raise ValueError('malformed process visibility row')
        pid,ppid,rss=(c.parse_number(v) for v in words[:3])
        if not pid or pid in pids:raise ValueError('duplicate/zero process visibility PID')
        pids.add(pid)
    if not pids:raise ValueError('missing process visibility')
    for line in services.splitlines():
        words=line.split()
        if len(words)<4 or not words[0].endswith('.service') or words[2:4]!=['active','running']:
            raise ValueError('malformed/racing service visibility')
    return dict(schema='ResourceRssGOv3-visibility-v1',cgroups=rows,
        bounded_reserved_bytes=reserved,projected_reserved_bytes=c.add((reserved,requested)),
        process_visibility=processes,service_visibility=services,docker_visibility=containers,
        allowed=True,reserve_check=True,
        compatibility_flags='visibility/inventory completed only; no legacy reserve/accounting decision')

def read_only_admission(*,phase):
    if phase not in ('prospective','inside-scope'):raise ValueError('unknown phase')
    requested=4*c.GIB if phase=='prospective' else 0
    old=None;snapshots={};failures={}
    try:old=visibility(requested)
    except (OSError,ValueError,TypeError,KeyError,subprocess.SubprocessError) as exc:
        failures['visibility']=dict(error=str(exc),type=type(exc).__name__)
    for label in ('before','after'):
        try:snapshots[label]=identity['scan_bound']()
        except (OSError,ValueError,TypeError,KeyError,IndexError) as exc:
            snapshots[label]=None
            failures[label]=dict(error=str(exc),type=type(exc).__name__,errno=getattr(exc,'errno',None),
                raw_inputs=getattr(exc,'partial_raw_inputs',{}),read_attempts=getattr(exc,'read_attempts',[]))
    decision=policy.evaluate(old,snapshots['before'],snapshots['after'],requested,phase=phase,
        expected=EXPECTED if phase=='inside-scope' else None,
        expected_unit=UNIT+'.scope' if phase=='inside-scope' else None)
    if failures:decision.update(allowed=False,collection_failures=failures)
    return dict(api_version='ResourceRssGOv320261025-v1',collector_pid=os.getpid(),decision=decision,
                snapshots=snapshots,original_legacy=old,print_axioms='N/A; formal budget ZERO')
