#!/usr/bin/env python3
"""One immutable, capped NUC run. Invoke via systemd-run; no keys are touched."""
import argparse, hashlib, json, os, re, signal, subprocess, time
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('plan');a=ap.parse_args();plan=json.loads(Path(a.plan).read_text())
cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().split('0::',1)[1].strip().lstrip('/')
limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max']}
assert limits['memory.swap.max']=='0' and int(limits['memory.high'])<=int(limits['memory.max'])<=8*2**30,limits
# Include only topmost populated finite reservations, avoiding nested double counting.
finite=[]
for p in Path('/sys/fs/cgroup').rglob('memory.max'):
 try:
  if p.read_text().strip()!='max' and 'populated 1' in (p.parent/'cgroup.events').read_text():finite.append((str(p.parent),int(p.read_text())))
 except OSError:pass
reservations=[(p,n) for p,n in finite if not any(p.startswith(q+'/') for q,_ in finite if q!=p)]
assert sum(n for _,n in reservations)<=50*2**30,reservations
# Do not launch while another Lean/compiler/probe is running outside this scope.
foreign=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit():continue
 try:
  name=(p/'exe').resolve().name;pcg=(p/'cgroup').read_text()
  if name in {'lean','lake','cargo','rustc','aeneas','charon','cargo-build-sbf','rust-lld','ld.lld'} and str(cg).removeprefix('/sys/fs/cgroup') not in pcg:foreign.append((p.name,name))
 except OSError:pass
assert not foreign,foreign
out=Path(plan['out']);out.mkdir(parents=True,exist_ok=False)
env=dict(os.environ,**plan.get('env',{}));before=Path('/proc/meminfo').read_text();start=time.monotonic()
with (out/'stdout.log').open('w') as stdout,(out/'stderr.log').open('w') as stderr:
 proc=subprocess.Popen(['/usr/bin/time','-v','-o',str(out/'time.log'),*plan['command']],cwd=plan['cwd'],env=env,stdout=stdout,stderr=stderr,start_new_session=True)
 peak=0;stopped=False
 while proc.poll() is None:
  rss=0
  for pid in (cg/'cgroup.procs').read_text().split():
   try:rss+=int(Path('/proc',pid,'statm').read_text().split()[1])*os.sysconf('SC_PAGE_SIZE')
   except (OSError,IndexError):pass
  peak=max(peak,rss)
  if rss>=8*2**30 or time.monotonic()-start>600:
   os.killpg(proc.pid,signal.SIGKILL);stopped=True;break
  time.sleep(.2)
 status=proc.wait()
timing=(out/'time.log').read_text()
def metric(name):
 m=re.search(re.escape(name)+r':\s*(\d+)',timing);return int(m[1]) if m else None
receipt=dict(plan,exit_status=status,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size (kbytes)'),process_swaps=metric('Swaps'),peak_aggregate_rss_bytes_sampled=peak,cgroup=str(cg),limits=limits,reservations=reservations,cgroup_memory_peak_bytes=int((cg/'memory.peak').read_text()),cgroup_swap_current=(cg/'memory.swap.current').read_text().strip(),system_swap_before=[x for x in before.splitlines() if x.startswith('Swap')],system_swap_after=[x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('Swap')],mandatory_review_stop=stopped,print_axioms=plan.get('print_axioms','N/A: no Lean compilation'),runner_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt));raise SystemExit(status if status>=0 else 128-status)
