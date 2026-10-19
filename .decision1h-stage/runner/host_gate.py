#!/usr/bin/env python3
"""Read-only, separately reviewed exclusive-host launch gate. No compiler calls."""
import argparse, datetime, fcntl, hashlib, json, os, re
from pathlib import Path

LOCK='/tmp/aspis-r0-lean.lock'
PARALLEL_LOCK='/tmp/aspis-r1-recut-a.lock'
PARALLEL_AUTHORIZATION='User explicitly instructed: just do it in parallel; foreign Lean/build activity is permitted, task resource caps remain mandatory.'
BUILD_NAMES={'lean','lake','cargo','rustc','aeneas','charon','charon-driver','rust-lld','ld.lld','clang','cc','gcc','cargo-build-sbf','r18_replay','r18_replay_fresh','pool_gate'}
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def processes():
    out={}
    for p in Path('/proc').iterdir():
        if not p.name.isdigit(): continue
        try:
            s=(p/'stat').read_text(); tail=s[s.rfind(')')+2:].split()
            out[int(p.name)]={'pid':int(p.name),'ppid':int(tail[1]),'comm':(p/'comm').read_text().strip(),'argv':(p/'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace')}
        except (OSError,ValueError): pass
    return out
def ancestors(ps,pid):
    result=set()
    while pid in ps and pid not in result:
        result.add(pid);pid=ps[pid]['ppid']
    return result
def descendants(ps,pid):
    result={pid}
    while True:
        nxt=result|{p for p,v in ps.items() if v['ppid'] in result}
        if nxt==result:return result
        result=nxt
def process_cgroup(pid):
    try:return Path('/proc',str(pid),'cgroup').read_text().strip()
    except OSError:return None
def activity(exclude=(),own_job=None,own_cgroup=None):
    ps=processes(); excluded=ancestors(ps,os.getpid())|set(exclude);found=[]
    if own_job is not None:excluded |= descendants(ps,own_job)
    for pid,p in ps.items():
        if pid in excluded:continue
        # Exact dedicated scope equality, never the shared user.slice prefix.
        if own_cgroup is not None and process_cgroup(pid)==own_cgroup:continue
        comm=p['comm'];argv=p['argv']
        if comm in BUILD_NAMES or comm.startswith(('aeneas','charon','aspis','r18_replay','pool_gate')) or (comm.startswith('python') and re.search(r'/(?:run|launch|prove)[^ /]*\.py\b',argv) and 'aspis' in argv):
            p=dict(p,cgroup=process_cgroup(pid));found.append(p)
    return found
def reservations():
    found=[]
    for p in Path('/sys/fs/cgroup').rglob('memory.max'):
        try:
            value=p.read_text().strip(); events=(p.parent/'cgroup.events').read_text()
            if value!='max' and 'populated 1' in events:found.append({'cgroup':str(p.parent),'max':int(value)})
        except OSError:pass
    # Count outer capped scopes only: descendants are already covered.
    return [v for v in found if not any(v['cgroup'].startswith(o['cgroup']+'/') for o in found if o!=v)]
def assess(root,revision,locked=False,exclude=(),parallel_authorized=False):
    root=Path(root);errors=[];active=activity(exclude)
    if active and not parallel_authorized:errors.append('external build/proof/replay activity')
    lock_path=PARALLEL_LOCK if parallel_authorized else LOCK
    lock_ok=locked
    if not locked:
        with open(lock_path,'a+') as fd:
            try:fcntl.flock(fd,fcntl.LOCK_EX|fcntl.LOCK_NB);lock_ok=True
            except BlockingIOError:errors.append('shared host lock occupied')
    scopes=reservations();total=sum(v['max'] for v in scopes)
    # The inner launch preflight already occupies its own8GiB scope.
    requested=0 if locked else 8589934592
    if total+requested>=55*1024**3:errors.append('aggregate caps reach/exceed55GiB')
    mem={line.split(':')[0]:int(line.split()[1])*1024 for line in Path('/proc/meminfo').read_text().splitlines() if line.split()[1].isdigit()}
    if mem['MemAvailable']<10*1024**3:errors.append('less than10GiB available RAM')
    manifest=json.loads((root/'source-files.json').read_text())
    if manifest['revision']!=revision:errors.append('source manifest revision mismatch')
    bad=[p for p,h in manifest['files'].items() if not (root/'source'/p).is_file() or sha(root/'source'/p)!=h]
    if bad:errors.append('source manifest byte mismatch')
    tools=json.loads((root/'tool-pins.json').read_text())
    badtools=[p for p,h in tools['pins'].items() if not Path(p).is_file() or sha(p)!=h]
    if badtools:errors.append('tool file hash mismatch')
    inputs=json.loads((root/'input-files.json').read_text())
    badinputs=[p for p,h in inputs['files'].items() if not (root/p).is_file() or sha(root/p)!=h]
    if badinputs:errors.append('baseline/fixture/runner input hash mismatch')
    return {'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'revision':revision,'status':'PASS' if not errors else 'BLOCKED','errors':errors,'active':active,'foreign_activity_allowed':parallel_authorized,'user_authorization':PARALLEL_AUTHORIZATION if parallel_authorized else None,'lock_path':lock_path,'lock_available_or_held':lock_ok,'reservations':scopes,'aggregate_max':total,'new_reservation':requested,'memory':mem,'source_mismatches':bad,'tool_mismatches':badtools,'input_mismatches':badinputs,'source_manifest_sha256':sha(root/'source-files.json'),'input_manifest_sha256':sha(root/'input-files.json'),'gate_source_sha256':sha(__file__)}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--root',required=True);p.add_argument('--revision',required=True);p.add_argument('--output',required=True);p.add_argument('--parallel-authorized',action='store_true');a=p.parse_args()
    result=assess(a.root,a.revision,parallel_authorized=a.parallel_authorized);out=Path(a.output)
    with out.open('x') as fd:json.dump(result,fd,indent=2);fd.write('\n')
    print(json.dumps(result,indent=2));raise SystemExit(0 if result['status']=='PASS' else 2)
