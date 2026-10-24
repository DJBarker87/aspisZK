"""Job-only metadata live boundary. Pure reviewed evaluator remains unchanged."""
import json
from pathlib import Path
import subprocess
from ResourceAdmit_sources import load

c, go, identity, inventory = load()
EXPECTED=dict(high=3*c.GIB,cap=4*c.GIB,swap_max=0,tasks_max=64)
UNIT='resource-admit-20261024'
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
        containers.append(dict(state,id=cid,host_config=config))
    if not processes.strip():raise ValueError('missing process visibility')
    return dict(schema='ResourceAdmit-visibility-v1',cgroups=rows,
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
    decision=go['evaluate'](old,snapshots['before'],snapshots['after'],requested,phase=phase,
                            expected=EXPECTED if phase=='inside-scope' else None)
    if phase=='inside-scope' and decision['allowed']:
        # Job binding supplements unchanged pure API: another identically capped
        # .scope cannot stand in for this one independently created unit.
        path=decision['scope_binding']['self_identity']['path']
        if Path(path).name!=UNIT+'.scope':
            failures['unit']=dict(error='actual own scope unit differs from preregistration')
    if failures:decision.update(allowed=False,collection_failures=failures)
    return dict(api_version='ResourceAdmit20261024-v1',decision=decision,
                snapshots=snapshots,original_legacy=old,print_axioms='N/A; formal budget ZERO')
