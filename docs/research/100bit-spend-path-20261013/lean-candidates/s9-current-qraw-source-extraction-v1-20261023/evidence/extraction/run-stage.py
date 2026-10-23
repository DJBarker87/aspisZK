from pathlib import Path
import hashlib, json, os, re, signal, subprocess, sys, time
W=Path(__file__).resolve().parent
phase=sys.argv[1]
assert phase in {'charon','aeneas'}
SRC=Path('/home/dombarker/project-offloads/s9-explicit-helper-v1-20261023/attempt32-v38-complete-source/work/src')
CRATE=SRC/'crates/aspis-r1-cost-probe'
OUT=W/'runs'/phase
OUT.mkdir(parents=True,exist_ok=False)
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
weights=CRATE/'src/weights.rs'; fast=CRATE/'src/fast_pairing.rs'; lock=SRC/'Cargo.lock'
source_manifest=SRC/'s9-candidate-source-manifest.json'; candidate=json.loads(source_manifest.read_text())
expected_files=candidate['files']; actual_files={rel:sha(SRC/rel) for rel in expected_files}
assert actual_files==expected_files, {p:{'expected':expected_files[p],'actual':actual_files[p]} for p in expected_files if expected_files[p]!=actual_files[p]}
expected={'weights.rs':'ab55509e54218a2bfe7dd2d5e1b14216e3303961c16c181ce2e03d40f6b7678b','fast_pairing.rs':'7f75b58bfcaf7f586acb0152671e42565a549a8ace2b90dab794533dcdb6335e','Cargo.lock':'5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'}
assert sha(weights)==expected['weights.rs']; assert sha(fast)==expected['fast_pairing.rs']; assert sha(lock)==expected['Cargo.lock']
G=1024**3
cgline=Path('/proc/self/cgroup').read_text().strip(); assert cgline.startswith('0::'),cgline
cg=Path('/sys/fs/cgroup')/cgline[3:].lstrip('/')
limits={k:(cg/k).read_text().strip() for k in ('memory.high','memory.max','memory.swap.max')}
assert limits=={'memory.high':str(1*G),'memory.max':str(2*G),'memory.swap.max':'0'},limits
TOOL=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016')
charon=TOOL/'charon-target/release/charon'; aeneas=TOOL/'bin/aeneas'
assert sha(charon)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert sha(aeneas)=='959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3'
if phase=='charon':
 out=W/'runs/charon/actual-raw.llbc'
 cmd=[str(charon),'cargo','--preset','aeneas','--mir','built','--sysroot','default',
      '--start-from','crate::fast_pairing::canonical::_::raw',
      '--dest-file',str(out),'--','--manifest-path',str(CRATE/'Cargo.toml'),'--locked','--offline','--release','--lib','--no-default-features','--features','private-leaf-salts','--jobs','1']
 assert cmd[cmd.index('--start-from')+1]=='crate::fast_pairing::canonical::_::raw',cmd
 assert '--opaque' not in cmd,cmd
 cwd=SRC; env=os.environ.copy(); env['CARGO_TARGET_DIR']='/home/dombarker/project-offloads/s4-three-source-review-20261022/run1/work/native-target'; env['CARGO_NET_OFFLINE']='true'
 expected_work='focused actual H5 Q.raw source extraction, exact fast7f75/weightsab555; warm Cargo target, intended own-crate MIR pass only, no cold dependency build'
else:
 llbc=W/'runs/charon/actual-raw.llbc'; assert llbc.is_file()
 out=W/'runs/aeneas/generated'
 cmd=[str(aeneas),'-sequential','-no-progress-bar','-abort-on-error','-print-error-diagnostics','-log-debug','InterpJoin','-backend','lean','-namespace','AspisR1S9ActualRawCutV1','-dest',str(out),'-subdir','AspisR1S9ActualRawCutV1','-split-files','-emit-json',str(llbc)]
 cwd=OUT.parent/'charon'; env=os.environ.copy(); expected_work='focused Aeneas translation of fresh actual H5 Q.raw LLBC; actual direct input casts and partial closure, no invented raw body'
for k in ('RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS'): env.pop(k,None)
command={'phase':phase,'argv':cmd,'cwd':str(cwd),'limits':limits,'cgroup':str(cg),'source_sha256s':expected,'candidate_source_manifest_sha256':sha(source_manifest),'candidate_source_hashes':actual_files,
         'charon_sha256':sha(charon),'aeneas_sha256':sha(aeneas),'expected_work':expected_work,
         'workspace_revision':candidate['research_head']}
(OUT/'command.json').write_text(json.dumps(command,indent=2)+'\n')
(OUT/'environment.json').write_text(json.dumps({'PATH':env.get('PATH'),'CARGO_NET_OFFLINE':env.get('CARGO_NET_OFFLINE'),'CARGO_TARGET_DIR':env.get('CARGO_TARGET_DIR')},indent=2)+'\n')
before=(cg/'memory.events').read_text(); start=time.monotonic(); timed=False
with (OUT/'stdout.log').open('x') as stream:
 p=subprocess.Popen(['/usr/bin/time','-v','-o',str(OUT/'time.log'),*cmd],cwd=cwd,env=env,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
 while p.poll() is None:
  if time.monotonic()-start>600:
   timed=True; os.killpg(p.pid,signal.SIGTERM)
   try:p.wait(timeout=5)
   except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL); p.wait()
   break
  time.sleep(.2)
status=p.wait()
t=(OUT/'time.log').read_text(); m=re.search(r'Maximum resident set size \(kbytes\): (\d+)',t)
receipt={**command,'exit_status':status,'timed_out':timed,'wall_seconds':round(time.monotonic()-start,3),
         'peak_process_rss_kib':int(m.group(1)) if m else None,'scope_memory_peak_bytes':int((cg/'memory.peak').read_text()),
         'scope_swap_current_bytes':int((cg/'memory.swap.current').read_text()),'memory_events_before':before,
         'memory_events_after':(cg/'memory.events').read_text(),'finished_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
if phase=='charon' and out.exists():
 obj=json.loads(out.read_text()); fds=obj.get('translated',{}).get('fun_decls',[])
 receipt.update({'llbc_sha256':sha(out),'llbc_has_errors':obj.get('has_errors'),'llbc_fun_decl_count':len(fds),
  'pair_root_present':any("'pair'" in str(f.get('item_meta',{}).get('name')) for f in fds),
  'helper_present':any("'factored_s2_libra_weights'" in str(f.get('item_meta',{}).get('name')) for f in fds)})
if phase=='aeneas' and (out/'translation.json').exists():
 tr=json.loads((out/'translation.json').read_text()); funcs=tr.get('functions',[]); files=list(out.rglob('*.lean'))
 text='\n'.join(p.read_text() for p in files)
 receipt.update({'translation_sha256':sha(out/'translation.json'),'translation_function_count':len(funcs),
  'translation_functions':funcs,'lean_file_hashes':{str(p.relative_to(W)):sha(p) for p in files},
  'has_pair': 'pair' in text.lower(),'has_helper':'factored_s2_libra_weights' in text,
  'has_raw': 'raw' in text.lower()})
 assert funcs and receipt['has_raw']
(OUT/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
sys.exit(status)
