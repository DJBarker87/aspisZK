#!/usr/bin/env python3
"""PCXR_ host admission check. Usage: pcxr_admit.py OUT.json. Exit 0 only if allowed:true.
Gates (brief): whole-host lean/extraction scopes < 6; Stream C scopes < 5 (Stream C = scope with a process whose cwd is under
project-offloads/codex-pc-); free disk on project-offloads >= 45 GB; running reservation + 8 GiB <= 55 GiB (delegated to the
unchanged S2H_reservation.py, which also honours QUIET_WINDOW.json). Read-only."""
import json,os,pathlib,subprocess,sys,shutil,time
PO='/home/dombarker/project-offloads'
RES='/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py'
out=pathlib.Path(sys.argv[1])
def sc(*a):return subprocess.run(['systemctl','--user',*a],capture_output=True,text=True).stdout
units=[l.split()[0] for l in sc('list-units','--type=scope','--state=running','--no-legend','--no-pager').splitlines() if l.strip()]
host=[];streamc=[]
for u in units:
    cg=sc('show',u,'-p','ControlGroup','--value').strip();p=pathlib.Path('/sys/fs/cgroup'+cg)
    try:pids=(p/'cgroup.procs').read_text().split()
    except OSError:continue
    kinds=set()
    for pid in pids:
        try:cwd=str(pathlib.Path('/proc/'+pid+'/cwd').resolve(strict=True));cmd=pathlib.Path('/proc/'+pid+'/cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace')
        except OSError:continue
        if cwd.startswith(PO+'/codex-'):kinds.add('host')
        if cwd.startswith(PO+'/codex-pc-'):kinds.add('c')
        if any(k in cmd for k in ('/bin/lean','charon','aeneas','rustc')) and not cmd.startswith('systemd'):kinds.add('host')
    if 'host' in kinds:host.append(u)
    if 'c' in kinds:streamc.append(u)
free=shutil.disk_usage(PO).free
r=subprocess.run(['python3',RES,str(out)+'.res'],capture_output=True,text=True)
try:res=json.loads(pathlib.Path(str(out)+'.res').read_text())
except Exception:res=dict(allowed=False,reason='reservation barrier unreadable: '+r.stdout[-200:]+r.stderr[-200:])
checks=dict(host_scopes=len(host)<6,streamc_scopes=len(streamc)<5,disk=free>=45_000_000_000,reservation=res.get('allowed') is True and r.returncode==0)
d=dict(allowed=all(checks.values()),checks=checks,host_scope_count=len(host),host_scopes=host,streamc_scope_count=len(streamc),streamc_scopes=streamc,
  disk_free_bytes=free,disk_floor_bytes=45_000_000_000,reservation_exit=r.returncode,
  reservation={k:res.get(k) for k in ('allowed','bounded_reserved_bytes','requested_bytes','safe_limit_bytes','reason','quiet_window_until')},utc=time.time())
out.write_text(json.dumps(d,indent=1)+'\n');print(json.dumps({k:d[k] for k in('allowed','checks')}))
sys.exit(0 if d['allowed'] else 78)
