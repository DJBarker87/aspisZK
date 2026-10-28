from pathlib import Path
import json,subprocess,hashlib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-native-prepare5-20261028'
payload=dict(B=B,source=json.loads((E/'NCH_SOURCE.json').read_text()),library=json.loads((E/'NCH_LIBRARY_RESOLVED.json').read_text()),last=json.loads((E/'NCH_K070/receipt.json').read_text()))
code='''from pathlib import Path
import json,hashlib,subprocess,shutil
x=json.loads(PAYLOAD);b=Path(x['B']);sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cache=x['source']['cache_imports'];cache_errors=[n for n,v in cache.items() if not Path(n).is_file() or sha(Path(n))!=v['sha256']]
lib_errors=[n for n,v in x['library'].items() if not Path(n).is_file() or sha(Path(n))!=v['sha256']]
sources=x['source']['source_sha256'];source_errors=[n for n,h in sources.items() if not (b/'NCH_src'/n).is_file() or sha(b/'NCH_src'/n)!=h]
last='NCH_src/crates/aspis-r1-cost-probe/src/NCH_candidate.rs';assert sha(b/last)==x['last']['source_hashes'][last]
rows=subprocess.check_output(['ps','-eo','pid,args'],text=True).splitlines();active=[r for r in rows if str(b) in r and any(s in r for s in ['cargo-kani','kani-compiler','S2W_run_host.py','S2W_lean_host.py'])]
assert not active,active
assert not cache_errors and not lib_errors and not source_errors,(cache_errors,lib_errors,source_errors)
removed=[]
for name in ['NCH_target','NCH_tmp']:
 p=b/name
 if p.exists():assert p.parent==b and not p.is_symlink();shutil.rmtree(p);removed.append(str(p))
cache_path=Path('/home/dombarker/project-offloads/codex-cx-prepare-cache-20261028');assert cache_path.is_dir()
out=dict(cache_imports_verified=len(cache),cache_errors=cache_errors,resolved_library_files_verified=len(x['library']),library_errors=lib_errors,source_files_verified=len(sources),source_errors=source_errors,active_own_provers=active,removed_build_scratch=removed,cache_retained=str(cache_path),new_own_cache_objects=[str(p) for p in cache_path.glob('NCH_*.olean')],shared_tmp_untouched=True,keys_or_wallets_touched=False)
(b/'NCH_POSTFLIGHT.json').write_text(json.dumps(out,indent=2)+'\\n');print(json.dumps(out))
'''.replace('PAYLOAD',repr(json.dumps(payload)))
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
(E/'NCH_POSTFLIGHT.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stdout+r.stderr
v=json.loads(r.stdout);(E/'NCH_POSTFLIGHT.json').write_text(json.dumps(v,indent=2)+'\n');print(json.dumps(v))
