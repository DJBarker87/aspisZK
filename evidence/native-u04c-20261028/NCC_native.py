"""Own serial controller: frozen scratch only; unchanged admission/backend."""
from pathlib import Path
import subprocess,json,sys,time,shlex,hashlib,tomllib
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-native-tx2j-20261028'
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def ssh(code,submitted=False):
 for n in range(11):
  try:
   r=subprocess.run(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,code],capture_output=True,text=True,timeout=None if submitted else 90)
  except subprocess.TimeoutExpired as exc:
   with (E/'NCC_NATIVE_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(trial=n,actual_exit=None,transport_timeout_seconds=90,submitted=submitted,command=code))+'\n')
   if n<10:time.sleep(60);continue
   raise SystemExit('STOP transport timeout exhausted')
  with (E/'NCC_NATIVE_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(trial=n,exit=r.returncode,submitted=submitted,stdout=(r.stdout if len(r.stdout)<120000 else {'sha256':hashlib.sha256(r.stdout.encode()).hexdigest(),'bytes':len(r.stdout.encode()),'retained_on_host':True}),stderr=r.stderr,command=code))+'\n')
  if r.returncode!=255 or submitted:return r
  if n<10:time.sleep(60)
 raise SystemExit('STOP transport exhausted')
def py(s,**kw):return ssh('python3 -c '+shlex.quote(s),**kw)
def admit(a):
 for n in range(11):
  s=f'''from pathlib import Path
import subprocess,json
b=Path({B!r}); b.mkdir(exist_ok=True)
p=b/{(a+'-barrier-'+str(n)+'.log')!r}
with p.open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
print(json.dumps(dict(exit=r.returncode,log=p.read_text(),reservation=json.loads((b/{(a+'-reservation.json')!r}).read_text()) if (b/{(a+'-reservation.json')!r}).exists() else None)))
'''
  r=py(s);assert r.returncode==0,r.stderr
  x=json.loads(r.stdout);(E/(a+f'-admission-{n}.json')).write_text(json.dumps(x,indent=2)+'\n')
  if x['reservation'] is None:
   if n==0:time.sleep(30);continue
   raise SystemExit('STOP missing reservation JSON')
  if x['exit']==0 and x['reservation'].get('allowed') is True:return
  if (x['exit']==78 or x['reservation'].get('allowed') is False) and n<10:time.sleep(180);continue
  raise SystemExit('STOP admission')
 raise SystemExit('STOP admission exhausted')
def collect(a):
 r=py(f'''from pathlib import Path
import json
b=Path({B!r}); print(json.dumps({{n:(b/n).read_text() for n in {[a+'/receipt.json',a+'/stdout.log',a+'/time.log']!r} if (b/n).exists()}}))''');assert r.returncode==0
 x=json.loads(r.stdout)
 for n,s in x.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
 assert a+'/receipt.json' in x,'STOP unresolved submitted run, do not resubmit'
 receipt=json.loads(x[a+'/receipt.json'])
 with (E/'NCC_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(receipt)+'\n')
 return receipt
def launch(a,kind,command,sources,timeout=180):
 admit(a)
 preflight=py('from pathlib import Path; b=Path('+repr(B)+'); (b/"NCC_tmp").mkdir(exist_ok=True); missing=[f for f in '+repr(sources)+' if not (b/f).is_file()]; assert not missing,missing')
 assert preflight.returncode==0,preflight.stdout+preflight.stderr
 target=command[command.index('--harness')+1] if '--harness' in command else 'cargo metadata'
 cfg=dict(attempt=a,kind=kind,module=target,sources=sources,command=command,timeout=timeout,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,env={'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_NET_OFFLINE':'true','CARGO_BUILD_JOBS':'1','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG':'0','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','CARGO_TARGET_DIR':B+'/NCC_target','TMPDIR':B+'/NCC_tmp'},deps_fingerprint={'frozen_source':REV},expected_time='Optimized compilation, then '+target+' solver gate; no field multiplication or protocol whole-buffer loop')
 (E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
 r=py(f'from pathlib import Path; p=Path({(B+"/"+a+".json")!r}); p.write_text({json.dumps(cfg,indent=2)!r})');assert r.returncode==0
 r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+shlex.quote(a+'.json'),submitted=True)
 (E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
 rc=collect(a);print(a,rc['exit_status'],rc['wall_seconds'],rc['peak_rss_kib'],flush=True);return rc
if (E/'NCC_PAUSE').exists():raise SystemExit('paused before any admission/submission')
if sys.argv[1]=='setup':
 admit('NCC_SETUP')
 paths=['Cargo.toml','Cargo.lock','crates','programs','audit/poseidon-pair-probe/program','xtask','tools/r1-builder-reference','docs/research/v8-r0-zk-20261009/refine/diffharness/tests/glue_gen.rs','docs/research/v8-r0-zk-20261009/c3/check','docs/research/v8-r0-zk-20261009/c3/build','docs/research/v8-r0-zk-20261009/z4']+['docs/research/v8-r0-zk-20261009/refine/'+n for n in ['writers','blockwriters','poseidon']]
 # One source scratch, no copied compiled corpus. Do not retry after data submission.
 r=ssh('test ! -e '+B+'/NBU_src');assert r.returncode==0,'scratch already exists; inspect rather than overwrite'
 r=ssh('mkdir -p '+B+'/NBU_src '+B+'/NCC_tmp');assert r.returncode==0
 a=subprocess.Popen(['git','archive',REV,*paths],stdout=subprocess.PIPE)
 r=subprocess.run(['ssh',H,'tar -xf - -C '+B+'/NBU_src'],stdin=a.stdout,capture_output=True,text=True);a.stdout.close();assert a.wait()==0 and r.returncode==0,r.stderr
 (E/'NCC_SETUP_TRANSFER.json').write_text(json.dumps(dict(revision=REV,paths=paths,exit=r.returncode,stderr=r.stderr),indent=2)+'\n')
 # New module and cfg-only inclusion exist solely in scratch; retain exact patch.
 patch=(E/'NCC_harness.patch').read_text()
 r=py(f'''from pathlib import Path
import subprocess
b=Path({B!r}); p=b/'NCC_harness.patch'; p.write_text({patch!r})
r=subprocess.run(['patch','-p1','--batch','--forward','-i',str(p)],cwd=b/'NBU_src'); assert r.returncode==0
''');assert r.returncode==0,r.stdout+r.stderr
elif sys.argv[1]=='run':
 a,harness=sys.argv[2:];assert len(list(E.glob('NCC_K*/receipt.json')))<60
 assert not harness.endswith(('::NCC_store688_gate','::NCC_store800_gate','::NBU_store688_gate','::NBU_store800_gate')),'retired timed-out shape; use isolated range/copy boundaries'
 frozen=subprocess.check_output(['git','show',REV+':Cargo.lock']);lockhash=hashlib.sha256(frozen).hexdigest()
 sources=['NBU_src/KMX_stubs.rs','NBU_src/crates/aspis-statement/src/KMX_stubs.rs','NBU_KMX_copy_stubs.patch','NBU_src/Cargo.lock','NBU_src/crates/aspis-statement/src/lib.rs','NBU_src/crates/aspis-statement/src/pool_v1/pair_terminal.rs','NBU_src/crates/aspis-statement/src/pool_v1/NBU_codecs.rs','NBU_src/crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs','NBU_src/crates/aspis-statement/src/pool_v1/NBU_more.rs','NBU_src/crates/aspis-statement/src/pool_v1/NBU_decode.rs','NBU_src/crates/aspis-statement/src/pool_v1/NCC_slots.rs','NBU_src/crates/aspis-statement/src/pool_v1/verifier_registry.rs']
 verify=py(f'''from pathlib import Path
import hashlib,json
b=Path({B!r});s=b/'NBU_src';p=b/'NBU_KMX_copy_stubs.patch'
assert hashlib.sha256(p.read_bytes()).hexdigest()=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
assert (s/'KMX_stubs.rs').read_bytes()==(s/'crates/aspis-statement/src/KMX_stubs.rs').read_bytes()
print('exact KMX patch and stub inclusion verified')
''');assert verify.returncode==0,verify.stdout+verify.stderr
 g=a.replace('_K','_G');rc=launch(g,'metadata',['/home/dombarker/.cargo/bin/cargo','metadata','--manifest-path',B+'/NBU_src/Cargo.toml','--locked','--offline','--format-version','1'],sources,120);assert rc['exit_status']==0
 # Cargo diagnostics are not JSON; parse the complete JSON output line only.
 lines=(E/g/'stdout.log').read_text().splitlines();m=next(json.loads(s) for s in lines if s.startswith('{') and '"packages"' in s)
 k={p['id']:json.dumps([p['name'],p['version'],p.get('source')],separators=(',',':')) for p in m['packages']}
 graph={'packages':sorted(k.values()),'edges':sorted([k[n['id']],sorted(k[d] for d in n['dependencies'])] for n in m['resolve']['nodes'])}
 expected=json.loads(Path('evidence/leaf-p6-11-20261027/LPm_frozen_graph.json').read_text())
 before=ssh('sha256sum '+B+'/NBU_src/Cargo.lock').stdout.split()[0]
 check=dict(graph_matches_frozen=graph==expected,lock_before_sha256=before,frozen_lock_sha256=lockhash,reference='evidence/leaf-p6-11-20261027/LPm_frozen_graph.json',offline=True)
 (E/(a+'-graph.json')).write_text(json.dumps(check,indent=2)+'\n');assert graph==expected and before==lockhash,'STOP frozen graph mismatch'
 meta=E/g/'stdout.log'; (E/g/'NCC_METADATA_OUTPUT_PIN.json').write_text(json.dumps({'sha256':hashlib.sha256(meta.read_bytes()).hexdigest(),'bytes':meta.stat().st_size,'raw_output_retained_on_host':B+'/'+g+'/stdout.log','normalized_graph_matches_frozen':True},indent=2)+'\n'); meta.unlink()
 rc=launch(a,'kani',['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NBU_src/crates/aspis-statement/Cargo.toml','--lib','-j','1','-Z','unstable-options','-Z','stubbing','-Z','function-contracts','--harness-timeout','90s','--exact','--harness',harness,'--output-format','terse'],sources,600)
 after=ssh('sha256sum '+B+'/NBU_src/Cargo.lock').stdout.split()[0];check.update(lock_after_sha256=after,lock_unchanged=after==before);(E/(a+'-graph.json')).write_text(json.dumps(check,indent=2)+'\n');assert after==before,'STOP lock drift'
 print((E/a/'stdout.log').read_text()[-900:])
 sys.exit(rc['exit_status'])
