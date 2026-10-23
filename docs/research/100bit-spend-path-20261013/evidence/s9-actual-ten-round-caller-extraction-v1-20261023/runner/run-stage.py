from pathlib import Path
import hashlib,json,os,re,signal,subprocess,sys,time
W=Path(__file__).resolve().parent
phase=sys.argv[1];assert phase in {'charon','aeneas'}
SRC=Path('/home/dombarker/project-offloads/s9-actual-semantic-rounds-source-cut-v1-20261023/attempt25/input')
OUT=W/'runs'/phase;OUT.mkdir(parents=True,exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((W/'source-manifest.json').read_text())
for row in manifest['files']:assert sha(SRC/row['path'])==row['sha256'],row['path']
assert sha(SRC/'crates/aspis-r1-cost-probe/src/r1_semantic.rs')=='cb6922614de8c9866b604aacf69f28d760da0143867906f6796b4b3c1d3abef0'
assert sha(SRC/'Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
G=1024**3
cgline=Path('/proc/self/cgroup').read_text().strip();assert cgline.startswith('0::')
cg=Path('/sys/fs/cgroup')/cgline[3:].lstrip('/')
limits={k:(cg/k).read_text().strip() for k in ('memory.high','memory.max','memory.swap.max')}
assert limits=={'memory.high':str(2*G),'memory.max':str(2*G),'memory.swap.max':'0'},limits
TOOL=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016')
charon=TOOL/'charon-target/release/charon';aeneas=TOOL/'bin/aeneas'
assert sha(charon)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert sha(aeneas)=='959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3'
root='crate::r1_semantic::semantic_rounds'
if phase=='charon':
 out=OUT/'actual-semantic-rounds.llbc'
 cmd=[str(charon),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from',root,
      '--opaque','crate::r1_wire::_::decode_k','--opaque','crate::r1_semantic::semantic_boundary','--opaque','crate::r1_semantic::semantic_value',
      '--dest-file',str(out),'--','--manifest-path',str(SRC/'Cargo.toml'),'--locked','--offline','--release','--lib','--no-default-features','--features','private-leaf-salts','-p','aspis-r1-cost-probe','--jobs','1']
 assert cmd.count('--start-from')==1 and cmd[cmd.index('--start-from')+1]==root
 cwd=SRC;env=os.environ.copy();env.update({'CARGO_TARGET_DIR':'/home/dombarker/project-offloads/s3-s9-scalar-fold-fullsysroot-v3-20261021/target','CARGO_NET_OFFLINE':'true','RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_BUILD_JOBS':'1'})
 expected_work='warm release MIR extraction of actual private semantic_rounds caller from untouched existing complete semantic source; no cold dependency build intended'
else:
 llbc=W/'runs/charon/actual-semantic-rounds.llbc';assert llbc.is_file()
 out=OUT/'generated'
 cmd=[str(aeneas),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR1ActualSemanticRoundCutV1','-dest',str(out),'-subdir','AspisR1ActualSemanticRoundCutV1','-split-files','-emit-json',str(llbc)]
 cwd=W;env=os.environ.copy();expected_work='focused translation of fresh actual semantic_rounds LLBC; opaque semantic arithmetic slots remain explicit'
for k in ('RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS'):env.pop(k,None)
command={'phase':phase,'argv':cmd,'cwd':str(cwd),'limits':limits,'cgroup':str(cg),'source_manifest_sha256':sha(W/'source-manifest.json'),'source_revision_at_launch':manifest['research_head'],'expected_work':expected_work,'tool_pins':{str(charon):sha(charon),str(aeneas):sha(aeneas)}}
(OUT/'command.json').write_text(json.dumps(command,indent=2)+'\n')
(OUT/'environment.json').write_text(json.dumps({k:env.get(k) for k in ['PATH','CARGO_TARGET_DIR','CARGO_NET_OFFLINE','CARGO_BUILD_JOBS','RUSTUP_TOOLCHAIN']},indent=2)+'\n')
before=(cg/'memory.events').read_text();start=time.monotonic();timed=False
with (OUT/'stdout.log').open('x') as stream:
 p=subprocess.Popen(['/usr/bin/time','-v','-o',str(OUT/'time.log'),*cmd],cwd=cwd,env=env,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
 while p.poll() is None:
  if time.monotonic()-start>600:
   timed=True;os.killpg(p.pid,signal.SIGTERM)
   try:p.wait(timeout=5)
   except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);p.wait()
   break
  time.sleep(.2)
status=p.wait();t=(OUT/'time.log').read_text();m=re.search(r'Maximum resident set size \(kbytes\): (\d+)',t)
rec={**command,'exit_status':status,'timed_out':timed,'wall_seconds':round(time.monotonic()-start,3),'peak_process_rss_kib':int(m.group(1)) if m else None,'scope_memory_peak_bytes':int((cg/'memory.peak').read_text()),'scope_swap_current_bytes':int((cg/'memory.swap.current').read_text()),'memory_events_before':before,'memory_events_after':(cg/'memory.events').read_text(),'finished_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
if phase=='charon' and out.exists():
 obj=json.loads(out.read_text());fds=obj.get('translated',{}).get('fun_decls',[])
 roots=[f for f in fds if "'semantic_rounds'" in str(f.get('item_meta',{}).get('name'))]
 rec.update({'llbc_sha256':sha(out),'llbc_bytes':out.stat().st_size,'llbc_has_errors':obj.get('has_errors'),'llbc_fun_decl_count':len(fds),'semantic_rounds_root_count':len(roots),'root_metadata':[{k:f.get(k) for k in ['def_id','item_meta','signature']} for f in roots],'root_body_nonempty':[bool(f.get('body')) for f in roots]})
if phase=='aeneas' and (out/'translation.json').exists():
 tr=json.loads((out/'translation.json').read_text());funcs=tr.get('functions',[]);roots=[f for f in funcs if f.get('rust_name')=='aspis_r1_cost_probe::r1_semantic::semantic_rounds']
 rec.update({'translation_sha256':sha(out/'translation.json'),'translation_function_count':len(funcs),'root_metadata':roots,'generated_files':{str(p.relative_to(W)):sha(p) for p in out.rglob('*.lean')}})
(OUT/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps({k:v for k,v in rec.items() if k in ['phase','exit_status','wall_seconds','peak_process_rss_kib','scope_memory_peak_bytes','scope_swap_current_bytes','llbc_sha256','llbc_has_errors','semantic_rounds_root_count','root_body_nonempty','translation_sha256','translation_function_count','root_metadata']},indent=2))
if status==0:
 assert not timed
 if phase=='charon':assert rec['semantic_rounds_root_count']==1 and all(rec['root_body_nonempty']) and rec['llbc_has_errors'] is False,rec
 else:assert len(rec['root_metadata'])==1 and rec['root_metadata'][0]['is_opaque'] is False,rec
sys.exit(status)
