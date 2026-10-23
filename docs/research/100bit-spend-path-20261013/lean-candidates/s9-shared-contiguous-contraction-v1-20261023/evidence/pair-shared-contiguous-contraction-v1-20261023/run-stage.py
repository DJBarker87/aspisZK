from pathlib import Path
import hashlib,json,os,re,signal,subprocess,sys,time
W=Path(__file__).resolve().parent
G=1024**3
C=json.loads((W/'config.json').read_text())
A=W/'attempt'; O=A/'objects'; O.mkdir(parents=True,exist_ok=True)
S=W/'sources'; sha=lambda b:hashlib.sha256(b).hexdigest()
lean=Path(C['lean'])
assert sha(lean.read_bytes())==C['lean_sha256']
roots=[O]+[Path(x) for x in C['lean_path']]
uniq=[];seen=set()
for p in roots:
 if str(p) not in seen: uniq.append(p);seen.add(str(p))
profile=[]
for m in ['QRawGeneratedDotPushConnectionV2','QRawActualCoefficientsFromBoundsV2','AspisR1EbyKDotPushSourceV1/LoopAdapter','OriginalDotPushRawLoopToLiteralV1']:
 rel=Path(*m.split('/')[0].split('.')).with_suffix('.olean') if '/' not in m else Path('AspisR1EbyKDotPushSourceV1/LoopAdapter.olean')
 matches=[p/rel for p in uniq if (p/rel).is_file()]
 profile.append({'module':m,'found':str(matches[0]) if matches else None,'sha256':sha(matches[0].read_bytes()) if matches else None})
assert profile[0]['found'], 'QRawGeneratedDotPushConnectionV2 missing from pinned S5 profile'
assert all(x['found'] for x in profile), profile
cgline=Path('/proc/self/cgroup').read_text().strip();assert cgline.startswith('0::')
cg=Path('/sys/fs/cgroup')/cgline[3:].lstrip('/')
limits={k:(cg/k).read_text().strip() for k in ('memory.high','memory.max','memory.swap.max')}
assert limits=={'memory.high':str(1*G),'memory.max':str(2*G),'memory.swap.max':'0'},limits
outdir=A/'objects';outdir.mkdir(exist_ok=True)
run={'source_revision':C['source_revision'],'lean':str(lean),'lean_sha256':C['lean_sha256'],'lean_path':':'.join(map(str,uniq)),'profile_selected_imports':profile,'limits':limits,'stages':[]}
for st in C['stages']:
 src=S/st['file']; h=sha(src.read_bytes()); obj=outdir/Path(*st['module'].split('.')).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
 ev=A/'evidence'/st['module'];ev.mkdir(parents=True,exist_ok=False)
 cmd=[str(lean),'-j1','-M','4400','-R',str(S),'-o',str(obj),str(src)]
 env=os.environ.copy();env['LEAN_PATH']=run['lean_path'];env['PATH']='/home/dombarker/.cargo/bin:/usr/bin:/bin'
 (ev/'command.json').write_text(json.dumps({'argv':cmd,'scope':'MemoryHigh=1GiB, MemoryMax=2GiB, MemorySwapMax=0; serial focused Lean targets'},indent=2)+'\n')
 pre={'target':st['module'],'source':str(src),'source_sha256':h,'source_revision':C['source_revision'],'object':str(obj),'lean':str(lean),'lean_sha256':C['lean_sha256'],'lean_path':run['lean_path'],'direct_selected_imports':profile,'limits':limits}
 (ev/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
 before=(cg/'memory.events').read_text();start=time.monotonic();peak=0;sw=0
 with (ev/'lean.log').open('w') as log, (ev/'time.log').open('w') as tf:
  p=subprocess.Popen(['/usr/bin/time','-v','-o',str(ev/'time.log'),*cmd],stdout=log,stderr=subprocess.STDOUT,env=env,start_new_session=True)
  while p.poll() is None:
   peak=max(peak,int((cg/'memory.peak').read_text()));sw=max(sw,int((cg/'memory.swap.current').read_text()))
   if time.monotonic()-start>600:
    os.killpg(p.pid,signal.SIGTERM)
    try:p.wait(timeout=3)
    except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL)
    break
   time.sleep(.1)
  status=p.wait()
 peak=max(peak,int((cg/'memory.peak').read_text()));sw=max(sw,int((cg/'memory.swap.current').read_text()))
 tm=(ev/'time.log').read_text();m=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',tm)
 receipt={'exit_status':status,'wall_seconds':round(time.monotonic()-start,3),'peak_process_rss_kib':int(m[1]) if m else None,'scope_memory_peak_bytes':peak,'scope_swap_peak_bytes':sw,'memory_events_before':before,'memory_events_after':(cg/'memory.events').read_text(),'source_sha256':h,'object_sha256':sha(obj.read_bytes()) if obj.exists() else None}
 (ev/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');run['stages'].append({'module':st['module'],**receipt});print(json.dumps({'module':st['module'],**receipt}),flush=True)
 if status: (A/'run.json').write_text(json.dumps(run,indent=2)+'\n');sys.exit(status)
(A/'run.json').write_text(json.dumps(run,indent=2)+'\n')
