#!/usr/bin/env python3
"""Build one existing collapse-remap candidate in an isolated warm tool copy.
No production or another session's tool sources are changed. This is a tool
candidate, not accepted source refinement; all interpreter checks remain on.
"""
from pathlib import Path
import hashlib,json,subprocess,time,os,shutil
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');W=H/'s1-collapse-tool-v3';W.mkdir(exist_ok=False);S=W/'source';base=Path('/home/dombarker/project-offloads/d18-aeneas-collapse-remap-v1-20261022/source');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['python3',str(H/'kit/reservation.py'),str(W/'admission-app-scopes.json')],check=True,stdout=subprocess.DEVNULL)
collector=Path('/home/dombarker/project-offloads/r1-circle-sample-wrapper-extraction-v2/collect-cgroups.py');r=subprocess.run(['python3',str(collector)],capture_output=True,text=True,check=True);inv=json.loads(r.stdout);(W/'admission-global.json').write_text(json.dumps(inv,indent=2)+'\n')
G=2**30;assert inv['effective_sum_bytes']+8*G<=48*G and inv['MemAvailable_kB']*1024>=14*G,'Global reservation admission denied'
# Warm source/cache copy. Never hardlink mutable tool source files.
subprocess.run(['cp','-a',str(base),str(S)],check=True)
p=S/'src/interp/InterpReduceCollapse.ml';old=p.read_text();needle='(AbsId.Map.find abs_id !nabs_map, i, pm, bid, ty)';assert old.count(needle)==1;p.write_text(old.replace(needle,'(get_id abs_id, i, pm, bid, ty)'))
(W/'candidate.patch').write_text(subprocess.run(['diff','-u',str(base/'src/interp/InterpReduceCollapse.ml'),str(p)],text=True,capture_output=True).stdout)
image='sha256:62b1a46c95d1866f21f76afc23eda952c5b1897da1b6ebbb8650129a9cc64144';name='aspis-s1-collapse-tool-v3';gate=W/'GO'
build='export OPAMJOBS=1 DUNEJOBS=1 AENEAS_VERSION=b59d5188-lean432-s1-collapse-remap-v3 OCAMLPARAM=_,ccopt=-static; cd /work/aeneas-full/src; exec /usr/bin/time -v -o /s1/time.log opam exec -- dune build main.exe --profile release -j 1'
entry='while [ ! -f /s1/GO ]; do sleep 0.1; done; '+build
cmd=['docker','create','--name',name,'--memory',str(8*G),'--memory-swap',str(8*G),'--pids-limit','64','-v','/usr/bin/time:/usr/bin/time:ro','-v',str(S)+':/work/aeneas-full','-v',str(W)+':/s1',image,'bash','-lc',entry]
cid=subprocess.check_output(cmd,text=True).strip();(W/'container-id.txt').write_text(cid+'\n');subprocess.run(['docker','start',cid],check=True,stdout=subprocess.DEVNULL)
try:
 info=json.loads(subprocess.check_output(['docker','inspect',cid],text=True))[0];pid=info['State']['Pid'];cg=Path('/sys/fs/cgroup')/Path('/proc/'+str(pid)+'/cgroup').read_text().strip().split('::',1)[1].lstrip('/');assert cid in str(cg),str(cg)
 subprocess.run(['sudo','-n','tee',str(cg/'memory.high')],input=str(6*G),text=True,stdout=subprocess.DEVNULL,check=True)
 limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']};assert limits=={'memory.high':str(6*G),'memory.max':str(8*G),'memory.swap.max':'0','pids.max':'64'},limits
 pins={str(p.relative_to(S)):sha(p) for p in S.rglob('*') if p.is_file() and '_build' not in p.parts and '.git' not in p.parts and p.suffix in ['.ml','.mli','.opam']}
 meta=dict(schema='focused-extractor-proof-packet-v1',image=image,command=cmd,build=build,source_root_revision=(base.parent/'evidence/source-root-head.txt').read_text().strip(),source_pins=pins,patch_sha256=sha(W/'candidate.patch'),collector_sha256=sha(collector),limits=limits,control_group=str(cg),qualification=__doc__,expected_time='Warm OCaml recompile of one changed interpreter module and executable relink; no Rust source/extraction or Lean replay.')
 (W/'input.json').write_text(json.dumps(meta,indent=2)+'\n');start=time.monotonic();gate.touch();peak=0;swap=0
 while True:
  state=json.loads(subprocess.check_output(['docker','inspect',cid],text=True))[0]['State']
  if cg.exists():
   peak=max(peak,int((cg/'memory.peak').read_text()));swap=max(swap,int((cg/'memory.swap.current').read_text()))
  if not state['Running']:break
  if time.monotonic()-start>300:subprocess.run(['docker','stop','--time','3',cid],check=True);raise RuntimeError('Focused tool build exceeded300s review limit')
  time.sleep(.5)
 logs=subprocess.check_output(['docker','logs',cid],stderr=subprocess.STDOUT);(W/'build.log').write_bytes(logs)
 code=state['ExitCode'];out=S/'src/_build/default/main.exe';receipt=dict(**meta,exit_status=code,wall_seconds=time.monotonic()-start,cgroup_memory_peak_bytes=peak,swap_bytes=swap,binary_sha256=sha(out) if code==0 else None,print_axioms='N/A tool build; not a theorem')
 import re
 timing=(W/'time.log').read_text() if (W/'time.log').exists() else ''
 rss=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',timing);swaps=re.search(r'Swaps:\s*(\d+)',timing)
 receipt.update(peak_rss_kib=int(rss[1]) if rss else None,process_swaps=int(swaps[1]) if swaps else None)
 (W/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:receipt[k] for k in ['exit_status','wall_seconds','cgroup_memory_peak_bytes','swap_bytes','binary_sha256']}));raise SystemExit(code)
finally:
 state=json.loads(subprocess.check_output(['docker','inspect',cid],text=True))[0]['State']
 if state['Running']:subprocess.run(['docker','stop','--time','3',cid],check=True)
