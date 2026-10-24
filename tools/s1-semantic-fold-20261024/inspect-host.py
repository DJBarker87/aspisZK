#!/usr/bin/env python3
"""Read-only preflight; never launches or authorizes a build."""
from pathlib import Path
import json,subprocess
R=Path(__file__).resolve().parents[2]
S=(R/'tools/s126-host-admission-20261024/HostAdmission.py').read_text()
S=S[:S.index("if __name__=='__main__'")]
S+='''
import os,hashlib
report=snapshot('/sys/fs/cgroup')
report['meminfo']={line.split(':')[0]:line.split(':')[1].strip() for line in pathlib.Path('/proc/meminfo').read_text().splitlines() if line.startswith(('MemTotal:','MemAvailable:','SwapTotal:','SwapFree:'))}
processes=[];seen=set()
for row in report['all_cgroups']:
 if not row.get('direct_process_count') or row.get('covering_capped_ancestor') is not None or row.get('memory.max')!='max':continue
 p=pathlib.Path('/sys/fs/cgroup')/row['path']/row.get('direct_ids_source','cgroup.procs')
 for item in p.read_text().split():
  if item in seen:continue
  seen.add(item);status=pathlib.Path('/proc')/item
  try:
   fields={line.split(':',1)[0]:line.split(':',1)[1].strip() for line in (status/'status').read_text().splitlines() if ':' in line}
   tgid=int(fields.get('Tgid',item))
   if ('tgid',tgid) in seen:continue
   seen.add(('tgid',tgid))
   entry={'tgid':tgid,'pid':int(item),'comm':(status/'comm').read_text().strip(),'cgroup':row['path'],'rss_bytes':int(fields.get('VmRSS','0 kB').split()[0])*1024}
   if entry['comm'].startswith('qemu'):
    argv=(status/'cmdline').read_bytes().decode().split(chr(0))
    entry['guest_memory_argument']=argv[argv.index('-m')+1] if '-m' in argv else 'not specified'
   processes.append(entry)
  except FileNotFoundError:processes.append({'pid':int(item),'raced_exit':True})
report['uncapped_direct_processes']=processes
report['uncapped_direct_rss_bytes']=sum(row.get('rss_bytes',0) for row in processes)
H=pathlib.Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
report['warm_source']={}
for sub in ['aspis-s1-claim-powers-cut-v1-20261024','s1-claim-word-partition-v1-20261024','s1-claim-word-checks-accepted-v1-20261024']:
 p=H/sub
 if p.is_dir():report['warm_source'][str(p)]={str(f.relative_to(p)):hashlib.sha256(f.read_bytes()).hexdigest() for f in [p/'Cargo.toml',p/'src/lib.rs'] if f.is_file()}
report['new_job_authorized']=False
print(json.dumps(report))
'''
r=subprocess.run(['ssh','-o','BatchMode=yes','-o','ConnectTimeout=10','dombarker@100.108.41.90','python3','-'],input=S,text=True,capture_output=True,timeout=60)
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/s1-semantic-fold-controls-20261024'
E.mkdir(exist_ok=True)
if r.returncode:raise RuntimeError(r.stderr)
m=json.loads(r.stdout);(E/'preflight-host.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({k:m[k] for k in ['timestamp_utc','reserved_bytes','meminfo','uncapped_direct_rss_bytes','warm_source','new_job_authorized']}))
print(json.dumps([r for r in m['uncapped_direct_processes'] if r.get('guest_memory_argument')]))
