"""Own serial controller: frozen scratch only; unchanged admission/backend."""
from pathlib import Path
import subprocess,json,sys,time,shlex,hashlib,tomllib
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-native-tx2d-20261027'
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def ssh(code,submitted=False):
 for n in range(11):
  r=subprocess.run(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,code],capture_output=True,text=True)
  with (E/'NBH_NATIVE_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(trial=n,exit=r.returncode,submitted=submitted,stdout=r.stdout,stderr=r.stderr,command=code))+'\n')
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
 return json.loads(x[a+'/receipt.json'])
def launch(a,kind,command,sources,timeout=180):
 admit(a)
 preflight=py('from pathlib import Path; b=Path('+repr(B)+'); missing=[f for f in '+repr(sources)+' if not (b/f).is_file()]; assert not missing,missing')
 assert preflight.returncode==0,preflight.stdout+preflight.stderr
 cfg=dict(attempt=a,kind=kind,module=command[-1],sources=sources,command=command,timeout=timeout,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,env={'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_NET_OFFLINE':'true','CARGO_BUILD_JOBS':'1','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG':'0','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','CARGO_TARGET_DIR':B+'/NBH_target','TMPDIR':B+'/NBH_tmp'},deps_fingerprint={'frozen_source':REV},expected_time='Optimized native compilation then named solver gate; no field multiplication')
 (E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
 r=py(f'from pathlib import Path; p=Path({(B+"/"+a+".json")!r}); p.write_text({json.dumps(cfg,indent=2)!r})');assert r.returncode==0
 r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+shlex.quote(a+'.json'),submitted=True)
 (E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
 rc=collect(a);print(a,rc['exit_status'],rc['wall_seconds'],rc['peak_rss_kib'],flush=True);return rc
if sys.argv[1]=='setup':
 admit('NBH_SETUP')
 paths=['Cargo.toml','Cargo.lock','crates','programs','audit/poseidon-pair-probe/program','xtask','tools/r1-builder-reference','docs/research/v8-r0-zk-20261009/refine/diffharness/tests/glue_gen.rs','docs/research/v8-r0-zk-20261009/c3/check','docs/research/v8-r0-zk-20261009/c3/build','docs/research/v8-r0-zk-20261009/z4']+['docs/research/v8-r0-zk-20261009/refine/'+n for n in ['writers','blockwriters','poseidon']]
 # One source scratch, no copied compiled corpus. Do not retry after data submission.
 r=ssh('test ! -e '+B+'/NBH_src');assert r.returncode==0,'scratch already exists; inspect rather than overwrite'
 r=ssh('mkdir -p '+B+'/NBH_src '+B+'/NBH_tmp');assert r.returncode==0
 a=subprocess.Popen(['git','archive',REV,*paths],stdout=subprocess.PIPE)
 r=subprocess.run(['ssh',H,'tar -xf - -C '+B+'/NBH_src'],stdin=a.stdout,capture_output=True,text=True);a.stdout.close();assert a.wait()==0 and r.returncode==0,r.stderr
 (E/'NBH_SETUP_TRANSFER.json').write_text(json.dumps(dict(revision=REV,paths=paths,exit=r.returncode,stderr=r.stderr),indent=2)+'\n')
 # New module and cfg-only inclusion exist solely in scratch; retain exact patch.
 patch=(E/'NBH_harness.patch').read_text()
 r=py(f'''from pathlib import Path
import subprocess
b=Path({B!r}); p=b/'NBH_harness.patch'; p.write_text({patch!r})
r=subprocess.run(['patch','-p1','--batch','--forward','-i',str(p)],cwd=b/'NBH_src'); assert r.returncode==0
''');assert r.returncode==0,r.stdout+r.stderr
elif sys.argv[1]=='run':
 a,harness=sys.argv[2:];assert len(list(E.glob('NBH_K*/receipt.json')))<30
 frozen=subprocess.check_output(['git','show',REV+':Cargo.lock']);lockhash=hashlib.sha256(frozen).hexdigest()
 sources=['NBH_src/Cargo.lock','NBH_src/crates/aspis-statement/src/pool_v1/verifier_registry.rs','NBH_src/crates/aspis-statement/src/pool_v1/NBH_registry.rs','NBH_src/crates/aspis-statement/src/pool_v1/pair_tree_profile.rs','NBH_src/crates/aspis-statement/src/pool_v1/NBH_digest.rs','NBH_src/crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs','NBH_src/crates/aspis-statement/src/pool_v1/NBH_terminal.rs']
 g=a.replace('_K','_G');rc=launch(g,'metadata',['/home/dombarker/.cargo/bin/cargo','metadata','--manifest-path',B+'/NBH_src/Cargo.toml','--locked','--offline','--format-version','1'],sources,120);assert rc['exit_status']==0
 # Cargo diagnostics are not JSON; parse the complete JSON output line only.
 lines=(E/g/'stdout.log').read_text().splitlines();m=next(json.loads(s) for s in lines if s.startswith('{') and '"packages"' in s)
 k={p['id']:json.dumps([p['name'],p['version'],p.get('source')],separators=(',',':')) for p in m['packages']}
 graph={'packages':sorted(k.values()),'edges':sorted([k[n['id']],sorted(k[d] for d in n['dependencies'])] for n in m['resolve']['nodes'])}
 expected=json.loads(Path('evidence/leaf-p6-11-20261027/LPm_frozen_graph.json').read_text())
 before=ssh('sha256sum '+B+'/NBH_src/Cargo.lock').stdout.split()[0]
 check=dict(graph_matches_frozen=graph==expected,lock_before_sha256=before,frozen_lock_sha256=lockhash,reference='evidence/leaf-p6-11-20261027/LPm_frozen_graph.json',offline=True)
 (E/(a+'-graph.json')).write_text(json.dumps(check,indent=2)+'\n');assert graph==expected and before==lockhash,'STOP frozen graph mismatch'
 rc=launch(a,'kani',['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NBH_src/crates/aspis-statement/Cargo.toml','--lib','-j','1','-Z','unstable-options','--harness-timeout','90s','--exact','--harness',harness,'--output-format','terse'],sources,600)
 after=ssh('sha256sum '+B+'/NBH_src/Cargo.lock').stdout.split()[0];check.update(lock_after_sha256=after,lock_unchanged=after==before);(E/(a+'-graph.json')).write_text(json.dumps(check,indent=2)+'\n');assert after==before,'STOP lock drift'
 print((E/a/'stdout.log').read_text()[-4000:])
