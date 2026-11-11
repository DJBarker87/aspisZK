#!/usr/bin/env python3
"""PCXR_ PIN2 cold-replay runner (host side). One module per capped scope; NOT launched until the lead says so.
Seed by reference: LEAN_PATH = <run>/view : L187/base_ref. <run>/view is a forest of SYMLINKS (no copies): L187 objects for modules
 outside the rebuild set, overlay-PIN2 objects, and new objects as they are built. Rebuild-set modules are absent from the view until built,
 so a stale resolution fails loudly. (Lean resolves a module through the FIRST search-path root holding its top-level namespace directory,
 so layering R0P across several LEAN_PATH roots does not work; found by the dry run, see PCXR_ATTEMPTS.)
Usage: pcxr_runner.py --workers N [--run-dir DIR] [--only m1,m2] [--probe-src FILE --probe-name NAME] [--max-failures 3]
 - workers <= 5 (Stream C share); every launch is gated by pcxr_admit.py (host scopes <6, Stream C scopes <5, disk >=45 GB,
   reservation <=55 GiB); refusal -> wait 180 s and retry (disk: 600 s, at most 6 times, then stop).
 - resumable: a module is skipped when its receipt (exit 0) has the same key (source sha + direct-import olean shas) and the
   olean still has the receipted sha. A FAILED receipt with an unchanged key is never rerun.
 - first failure blocks every transitive importer (BLOCKED_DEP); independent chains continue; --max-failures halts the run.
 - handover modules: if the overlay holds an olean for it, it is overlay-built (hash recorded at launch); else if
   <ws>/handover_src/<src_rel> exists it is compiled from there; else BLOCKED_HANDOVER (re-checked every tick).
 - touch <run>/PCXR_STOP to stop launching new scopes (running ones finish)."""
import argparse,hashlib,json,os,pathlib,subprocess,sys,time,collections
HERE=pathlib.Path(__file__).resolve().parent
WS=pathlib.Path('/home/dombarker/project-offloads/codex-pc-pin2-replay-20261111')
L187=pathlib.Path('/home/dombarker/project-offloads/codex-cx-replay-l187-20261109')
OVERLAY=pathlib.Path('/home/dombarker/project-offloads/pin2-overlay-20261111/overlay-PIN2')
SYSROOT='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
ap=argparse.ArgumentParser()
ap.add_argument('--workers',type=int,default=1);ap.add_argument('--run-dir',default=str(WS));ap.add_argument('--set',default=str(WS/'PCXR_REBUILD_SET.json'))
ap.add_argument('--only');ap.add_argument('--unedited',default='',help='comma list of handover modules to compile from the unchanged L187 source (the lead decides)');ap.add_argument('--probe-src');ap.add_argument('--probe-name');ap.add_argument('--max-failures',type=int,default=3)
ap.add_argument('--excluded-file',default=None);ap.add_argument('--revision',default='research 7b2db79493f + L187 plan 18a98720');ap.add_argument('--handover-src',default=str(WS/'handover_src'))
a=ap.parse_args();assert 1<=a.workers<=5
RUN=pathlib.Path(a.run_dir);OBJS=RUN/'objs';RC=RUN/'receipts';ADM=RUN/'admission';JOBS=RUN/'jobs';TMP=RUN/'tmp'
for d in (OBJS,RC,ADM,JOBS,TMP):d.mkdir(parents=True,exist_ok=True)
VIEW=RUN/'view';VIEW.mkdir(exist_ok=True)
LP=':'.join([str(VIEW),str(L187/'base_ref')])
def ev(**x):
    with (RUN/'PCXR_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict(utc=time.time(),**x))+'\n')
_hc={}
def sha(p):
    p=pathlib.Path(p);st=p.stat();k=(str(p),st.st_mtime_ns,st.st_size)
    if k not in _hc:_hc[k]=hashlib.sha256(p.read_bytes()).hexdigest()
    return _hc[k]
def rel(m):return m.replace('.','/')+'.olean'
def find(m):
    for root,tag in ((OBJS,'new'),(OVERLAY,'overlay'),(L187/'objs','l187')):
        p=root/rel(m)
        if p.is_file():return p,tag
    return None,None
def link(src,dst):
    dst=pathlib.Path(dst)
    try:
        if os.readlink(dst)==str(src):return 0
    except OSError:pass
    dst.parent.mkdir(parents=True,exist_ok=True);t=str(dst)+'.l%d'%os.getpid();os.symlink(str(src),t);os.replace(t,dst);return 1
def modof(rp):
    q=pathlib.PurePosixPath(rp);return '.'.join(list(q.parent.parts)+[q.name.split('.')[0]])
def sync_overlay():
    n=0
    for p in OVERLAY.rglob('*'):
        if p.is_file() and not (OBJS/p.relative_to(OVERLAY)).is_file():n+=link(p,VIEW/p.relative_to(OVERLAY))   # lead patch 4 2026-11-11: a host-built object always wins over an overlay copy
    return n
def link_new(m):
    for p in (OBJS/rel(m)).parent.glob(pathlib.Path(rel(m)).stem+'.*'):
        link(p,VIEW/p.relative_to(OBJS))
def build_view(rb):
    ovm={modof(str(p.relative_to(OVERLAY))) for p in OVERLAY.rglob('*') if p.is_file()};n=0
    for root,dirs,files in os.walk(L187/'objs'):
        for f in files:
            rp=str((pathlib.Path(root)/f).relative_to(L187/'objs'))
            if modof(rp) in rb or modof(rp) in ovm:continue
            n+=link(L187/'objs'/rp,VIEW/rp)
    return n+sync_overlay()
# tool pins at launch
tools={n:sha(HERE/n) for n in ('pcxr_runner.py','pcxr_admit.py','pcxr_scope_run.py')}
for n,p in (('S2H_reservation.py','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py'),('L187_plan.json',L187/'l187_plan.json'),('rebuild_set',a.set)):tools[n]=sha(p)
ov_manifest={str(p.relative_to(OVERLAY)):sha(p) for p in sorted(OVERLAY.rglob('*')) if p.is_file()}
(RUN/'PCXR_TOOLS_AT_LAUNCH.json').write_text(json.dumps(dict(tools=tools,overlay_manifest=ov_manifest,lean_path=LP,sysroot=SYSROOT,revision=a.revision,cargo_jobs='n/a (Lean only)'),indent=1))
RBSET={r['module'] for r in json.load(open(a.set))['modules']}
vn=build_view(RBSET)
ev(event='runner_start',view_links_changed=vn,args=vars(a),tools=tools,overlay_files=len(ov_manifest))
LAST_ADMIT=[0.0]
def launch(job,name):
    """admission -> systemd scope; returns Popen. Caller guarantees <= workers in flight."""
    waits=0
    while True:
        if (RUN/'PCXR_STOP').exists():return None
        if time.time()-LAST_ADMIT[0]<20.0:ev(event='admission_cached',target=name);break   # lead patch 2026-11-11: reuse an allowed admission for 20 s
        af=ADM/(name+'.json');r=subprocess.run(['python3',str(HERE/'pcxr_admit.py'),str(af)],capture_output=True,text=True)
        try:ad=json.loads(af.read_text())
        except Exception:ad=dict(allowed=False,checks={})
        ev(event='admission',target=name,exit=r.returncode,allowed=ad.get('allowed'),checks=ad.get('checks'),host=ad.get('host_scope_count'),streamc=ad.get('streamc_scope_count'),disk_free=ad.get('disk_free_bytes'))
        if r.returncode==0 and ad.get('allowed') is True:LAST_ADMIT[0]=time.time();break
        if ad.get('checks',{}).get('disk') is False:
            waits+=1
            if waits>6:ev(event='stop',reason='disk below 45 GB after 6 waits');sys.exit(3)
            time.sleep(600)
        else:time.sleep(180)
    unit='pcxr-%s-%d'%(hashlib.sha256(name.encode()).hexdigest()[:10],int(time.time()))
    job['unit']=unit;jf=JOBS/(name+'.json');jf.write_text(json.dumps(job))
    p=subprocess.Popen(['systemd-run','--user','--scope','--quiet','--unit',unit,'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(HERE/'pcxr_scope_run.py'),str(jf)],cwd=str(WS),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    for _ in range(150):
        if p.poll() is not None:break   # wait until the scope is populated so the next admission sees it
        if subprocess.run(['systemctl','--user','is-active','--quiet',unit+'.scope']).returncode==0:break
        time.sleep(0.2)   # lead patch 3 2026-11-11: finer poll, same 30 s bound
    ev(event='launch',target=name,unit=unit)
    return p
def base_job(name,src,root,expected,out,imports,key,l187obj,receipt):
    return dict(module=name,target=name,src=str(src),root=str(root),expected_source_sha256=expected,out_olean=str(out),imports=imports,import_key=key,
      l187_obj=str(l187obj) if l187obj else None,receipt=str(receipt),lean=SYSROOT+'/bin/lean',sysroot=SYSROOT,lean_path=LP,tmpdir=str(TMP),cwd=str(WS),source_revision=a.revision)
if a.probe_src:   # scratch probe (dry run only): one scope, no graph
    src=pathlib.Path(a.probe_src).resolve();n=a.probe_name;imps={}
    for l in src.read_text().splitlines():
        if l.startswith('import '):
            i=l.split()[1];p,t=find(i);imps[i]=dict(sha256=sha(p),origin=t,path=str(p)) if p else None
    job=base_job(n,src,src.parent,None,OBJS/'probe'/(n+'.olean'),imps,hashlib.sha256(json.dumps(imps,sort_keys=True).encode()).hexdigest(),None,RC/(n+'.json'))
    p=launch(job,'probe_'+n);out,_=p.communicate();ev(event='result',target=n,exit=p.returncode,out=out[-300:]);print(out);sys.exit(p.returncode)
S=json.load(open(a.set));M={r['module']:r for r in S['modules']};order=[r['module'] for r in S['modules']]
if a.only:
    keep=a.only.split(',');assert all(k in M for k in keep),[k for k in keep if k not in M];order=keep
sel=set(order)
rdeps=collections.defaultdict(list)
for m in order:
    for i in M[m]['imports_rebuild']:
        if i in M:rdeps[i].append(m)
st={m:'pending' for m in order};why={}
if a.excluded_file:
    _x=json.load(open(a.excluded_file))
    for m in _x['excluded']:
        if m in st:st[m]='excluded'
    for m in _x['blocked_by_excluded']:
        if m in st:st[m]='blocked_by_excluded'
    ev(event='exclusions',excluded=len(_x['excluded']),blocked_by_excluded=len(_x['blocked_by_excluded']))
def handover_src(m):
    p=pathlib.Path(a.handover_src)/M[m]['src_rel'];return p if p.is_file() else None
def block_descendants(m,reason):
    stack=[m]
    while stack:
        x=stack.pop()
        for y in rdeps[x]:
            if y in st and st[y] in('pending','blocked_handover'):st[y]='blocked_dep';why[y]=reason;stack.append(y)

_li={}
def lean_imports(path):
    try:st=path.stat()
    except OSError:return []
    k=(str(path),st.st_mtime_ns,st.st_size)
    if k in _li:return _li[k]
    out=[]
    try:txt=path.read_text(errors='replace')
    except OSError:return out
    for line in txt.splitlines():
        line=line.strip()
        if line.startswith('import '):out+=line[7:].split()
    _li[k]=out;return out   # lead patch 10 2026-11-11: memoised by (path, mtime, size)
_occ={}
def overlay_closure_imports(m):
    """rebuild-set modules reachable through overlay (new) modules' import lines, starting at overlay module m"""
    if m in _occ:return _occ[m]
    seen=set();st=[m];res=set()
    while st:
        x=st.pop()
        for tok in lean_imports(OVERLAY/(x.replace('.','/')+'.lean')):
            if tok in M:res.add(tok)
            elif (OVERLAY/rel(tok)).is_file() and tok not in seen:seen.add(tok);st.append(tok)
    _occ[m]=res;return res
def inputs(m):
    """-> (src,root,expected_sha,imports dict,key) or None if inputs not ready"""
    r=M[m]
    for i in r['imports_rebuild']+r['imports_overlay']:   # lead patch 11 2026-11-11: cheap in-memory pre-check before any file I/O
        if i in M and st.get(i)!='done':return 'DEP'
    ho=handover_src(m)
    if ho:src,root,exp=ho,pathlib.Path(a.handover_src),None
    elif r['role']=='handover_input' and m not in a.unedited.split(','):return 'HANDOVER'
    else:src,root,exp=L187/'src'/r['src_rel'],L187/'src',r['source_sha256']
    if not pathlib.Path(src).is_file():return 'HANDOVER'   # lead patch 9 2026-11-11: a module with no source anywhere is reported as blocked_handover, never a crash
    imps={}
    extra=[]   # lead patch 7/8 2026-11-11: handover sources may import modules the plan did not list; overlay (new) modules' own rebuild-set imports must be built too
    known=set(r['imports_rebuild']+r['imports_overlay']+r['imports_unchanged'])
    if ho:
        for tok in lean_imports(pathlib.Path(src)):
            if tok in M and tok not in known:extra.append(tok)
    for i0 in list(known)+list(extra):
        if i0 not in M and (OVERLAY/rel(i0)).is_file():
            for tok in overlay_closure_imports(i0):
                if tok in M and tok not in known and tok not in extra:extra.append(tok)
    for i in r['imports_rebuild']+r['imports_overlay']+r['imports_unchanged']+extra:
        p,t=find(i)
        if i in M and (t!='new' or st.get(i)!='done'):return 'DEP'   # lead patch 6: every rebuild-set import must be host-built and processed   # lead patches 2+5 2026-11-11: a rebuild-set import (also one the plan called overlay-provided) counts only when host-built and processed, or still overlay-provided
        if p is None:return 'DEP'
        imps[i]=dict(sha256=sha(p),origin=t,path=str(p))
    key=hashlib.sha256(('shape=symlink-view-v1\n'+sha(src)+'\n'+'\n'.join(i+':'+imps[i]['sha256'] for i in sorted(imps))).encode()).hexdigest()
    return src,root,exp,imps,key
running={};failures=0;done_n=0;t_start=time.time()
def finish(m,p):
    global failures,done_n
    out,_=p.communicate();rf=RC/(m+'.json')
    if rf.is_file():rc=json.loads(rf.read_text())
    else:
        rc=dict(module=m,status='FAIL_NO_RECEIPT',exit=p.returncode,diagnostics_tail=out[-1500:]);rf.write_text(json.dumps(rc,indent=1))
    ev(event='result',target=m,**{k:rc.get(k) for k in('status','exit','wall_seconds','peak_rss_kib','swaps','cgroup_memory_peak_bytes','olean_sha256','sorry_warnings')})
    if rc.get('status')=='PASS' and rc.get('sorry_warnings',0)==0:st[m]='done';done_n+=1;link_new(m)
    else:
        st[m]='failed';failures+=1;block_descendants(m,m);ev(event='failure_block',target=m)
while True:
    for m,p in list(running.items()):
        if p.poll() is not None:finish(m,p);del running[m]
    sync_overlay()
    stop=(RUN/'PCXR_STOP').exists() or failures>=a.max_failures
    # overlay-built / resume / readiness
    launched=False;waiting_ready=False
    for m in order:
        if st[m] in('pending','blocked_handover'):
            # lead patch 6 2026-11-11: overlay objects are never credited for rebuild-set modules; the host compiles every one
            x=inputs(m)
            if x=='HANDOVER':
                if st[m]!='blocked_handover':ev(event='blocked_handover',target=m)
                st[m]='blocked_handover';continue
            if x=='DEP':continue
            if st[m]=='blocked_handover':st[m]='pending'
            src,root,exp,imps,key=x;rf=RC/(m+'.json');out=OBJS/rel(m)
            if rf.is_file():
                old=json.loads(rf.read_text())
                if old.get('import_key')==key:
                    if old.get('status')=='PASS' and out.is_file() and sha(out)==old.get('olean_sha256'):st[m]='done';done_n+=1;link_new(m);ev(event='skip_resume',target=m);continue
                    if old.get('status')!='PASS':st[m]='failed';failures+=1;block_descendants(m,m);ev(event='failed_unchanged_not_rerun',target=m);continue
            if stop or len(running)>=a.workers:waiting_ready=True;continue   # lead patch 2026-11-11: fill all worker slots per tick
            job=base_job(m,src,root,exp,out,imps,key,L187/'objs'/rel(m),rf)
            p=launch(job,m)
            if p is None:continue
            st[m]='running';running[m]=p;launched=True
    if not running and not launched and (stop or not waiting_ready):break
    time.sleep(0.5 if launched else 2)   # lead patch 3 2026-11-11: shorter tick
cnt=collections.Counter(st.values())
summ=dict(counts=dict(cnt),failures=failures,wall_s=round(time.time()-t_start,1),blocked_handover=[m for m in order if st[m]=='blocked_handover'],failed=[m for m in order if st[m]=='failed'],why={k:v for k,v in list(why.items())[:50]})
(RUN/'PCXV_RUN_SUMMARY.json').write_text(json.dumps(summ,indent=1));ev(event='runner_end',**summ);print(json.dumps(summ))
