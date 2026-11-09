#!/usr/bin/env python3
"""L187 option-B batch runner (lead decision 2026-11-09). Runs INSIDE one capped scope
(MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64): a dependency-ordered sequence of
single-module `lean -j1 -M7000 -DElab.async=false` processes, 180 s each, stop at first failure,
no new module after 55 min. Objects from job overlays are never on LEAN_PATH: objs/ (replay
outputs) then base_ref/ (symlinks to the unchanged Mathlib/Aeneas/... base only); Init/Lean/Std
come from the pinned v4.32.0 sysroot."""
import json,os,sys,time,subprocess,hashlib,pathlib,re
W=pathlib.Path(__file__).resolve().parent
T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
b=sys.argv[1]; bd=W/'batches'/b
cfg=json.loads((bd/'batch.json').read_text())
rel=pathlib.Path('/sys/fs/cgroup')/next(l.split(':',2)[2].strip().lstrip('/') for l in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if l.startswith('0:'))
limits={n:(rel/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert limits=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},limits
overlay=json.loads((W/'overlay_sha.json').read_text())
env=dict(PATH='/usr/bin:/bin',LEAN_SYSROOT=T,LEAN_PATH=str(W/'objs')+':'+str(W/'base_ref'),TMPDIR=str(W/'tmp'))
res=open(bd/'results.jsonl','a'); start=time.monotonic()
def sha(p): return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def metric(t,name): return next((l.split(':',1)[1].strip() for l in t.splitlines() if name in l),None)
status='complete'
for k,m in enumerate(cfg['modules']):
  if time.monotonic()-start>55*60:
    for mm in cfg['modules'][k:]: res.write(json.dumps(dict(module=mm['module'],status='NOT_RUN_TIME'))+'\n')
    status='time_stop';break
  miss=[i for i in m['imports'] if not (W/'objs'/(i.replace('.','/')+'.olean')).is_file()]
  if miss:
    res.write(json.dumps(dict(module=m['module'],status='NOT_RUN_DEP_MISSING',missing=miss[:5]))+'\n');res.flush();continue
  src=W/'src'/m['src_rel']; out=W/'objs'/(m['src_rel'][:-5]+'.olean'); tmp=W/'tmp'/(b+'_'+str(k)+'.olean')
  out.parent.mkdir(parents=True,exist_ok=True)
  tf=bd/'time'/(str(k)+'.txt'); tf.parent.mkdir(exist_ok=True)
  cmd=[T+'/bin/lean','-j1','-M7000','-DElab.async=false','-R',str(W/'src'),'-o',str(tmp),str(src)]
  t0=time.monotonic()
  r=subprocess.run(['/usr/bin/time','-v','-o',str(tf),'timeout','180',*cmd],cwd=W,env=env,capture_output=True,text=True)
  wall=time.monotonic()-t0; tt=tf.read_text() if tf.exists() else ''
  log=(r.stdout+r.stderr)
  row=dict(module=m['module'],label=m['label'],status='PASS' if r.returncode==0 else 'FAIL',exit=r.returncode,wall_seconds=round(wall,3),
    peak_rss_kib=metric(tt,'Maximum resident set size'),swaps=metric(tt,'Swaps'),source=m['source'],source_sha256_host=sha(src),
    overlay_object=m['overlay'],overlay_sha256=overlay.get(m['module']),argv=cmd,
    sorry_warnings=len(re.findall(r"declaration uses 'sorry'",log)),diagnostics_tail=log[-3000:] if r.returncode!=0 else log[-600:])
  if r.returncode==0 and tmp.is_file():
    moved=[]
    for sib in sorted(tmp.parent.glob(tmp.name+'*')):
      dest=pathlib.Path(str(out)+sib.name[len(tmp.name):]); os.replace(sib,dest); moved.append(dest.name)
    for ext in ['.ir','.ilean','.c']:
      sib=tmp.with_suffix(ext)
      if sib.is_file(): dest=out.with_suffix(ext); os.replace(sib,dest); moved.append(dest.name)
    ovir=pathlib.Path(m['overlay'][:-len('.olean')]+'.ir')
    if ovir.is_file():
      myir=out.with_suffix('.ir')
      row.update(ir_present=myir.is_file(),ir_sha256=sha(myir) if myir.is_file() else None,ir_identical_to_overlay=(myir.is_file() and sha(myir)==sha(ovir)))
    h=sha(out); row.update(object_sha256=h,object_identical_to_overlay=(h==overlay.get(m['module'])),object_files=moved)
  else:
    for sib in list(tmp.parent.glob(tmp.name+'*'))+[tmp.with_suffix(e) for e in ['.ir','.ilean','.c']]:
      if sib.is_file(): sib.unlink()
  if r.returncode==0 and row.get('object_sha256') and not row.get('object_identical_to_overlay'):
    cf=W/'tmp'/(b+'_'+str(k)+'.cmp.tsv'); co=W/'tmp'/(b+'_'+str(k)+'.cmp.jsonl')
    cf.write_text(m['module']+'\t'+m['overlay']+'\t'+str(out)+'\n')
    cr=subprocess.run(['timeout','120',str(W/'tools'/'L187_Compare'),str(cf),str(co)],capture_output=True,text=True)
    try: cj=json.loads(co.read_text().splitlines()[0])
    except Exception: cj=dict(error='compare produced no result: exit %d %s'%(cr.returncode,cr.stderr[-300:]))
    row['decl_compare']=cj.get('result',cj)
    res_=cj.get('result',{})
    if m['label']=='COHERENCE_REPAIR':
      # statements frozen: only theorem proofs may differ from the overlay object
      row['coherence_repair']=dict(statements_identical=bool(res_.get('identical_except_theorem_proofs')),proofs_identical=bool(res_.get('identical_declarations')))
      if not res_.get('identical_except_theorem_proofs'): row['status']='DIVERGENT'
    elif not res_.get('identical_declarations'): row['status']='DIVERGENT'
    for x in (cf,co):
      if x.is_file(): x.unlink()
  elif r.returncode==0 and row.get('object_identical_to_overlay'):
    row['decl_compare']='byte-identical'
  res.write(json.dumps(row)+'\n');res.flush()
  if row['status']=='DIVERGENT':
    for mm in cfg['modules'][k+1:]: res.write(json.dumps(dict(module=mm['module'],status='NOT_RUN_BATCH_STOPPED'))+'\n')
    status='divergent_stop';break
  if r.returncode!=0:
    for mm in cfg['modules'][k+1:]: res.write(json.dumps(dict(module=mm['module'],status='NOT_RUN_BATCH_STOPPED'))+'\n')
    status='failure_stop';break
res.close()
(bd/'DONE.json').write_text(json.dumps(dict(status=status,wall_seconds=time.monotonic()-start,limits=limits,cgroup=str(rel),
  cgroup_memory_peak_bytes=(rel/'memory.peak').read_text().strip())))
