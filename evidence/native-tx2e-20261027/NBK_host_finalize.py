from pathlib import Path
import json,hashlib,subprocess,shlex
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-native-tx2e-20261027';H='dombarker@100.108.41.90';REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
assert len(list(E.glob('NBK_K*/receipt.json')))==60,'finalize only after native budget terminal'
rows=subprocess.check_output(['git','ls-tree','-r',REV,'--','crates','programs','Cargo.lock'],text=True).splitlines();expected={}
for row in rows:
 meta,path=row.split('\t',1)
 if meta.split()[1]!='blob':continue
 data=subprocess.check_output(['git','cat-file','blob',meta.split()[2]])
 expected[path]={'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
x=json.loads((E/'NBK_SYNC_MORE-payload.json').read_text());parent='crates/aspis-statement/src/pool_v1/pair_terminal.rs'
files={parent:x['original']+x['marker']+x['more'],'crates/aspis-statement/src/pool_v1/NBK_codecs.rs':(E/'NBK_codecs.rs.txt').read_text(),'crates/aspis-statement/src/pool_v1/NBK_more.rs':(E/'NBK_more.rs.txt').read_text()}
for p,s in files.items():data=s.encode();expected[p]={'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
code='''from pathlib import Path
import hashlib,json,shutil
b=Path(B_VALUE);cache=Path('/home/dombarker/project-offloads/codex-cx-leaf-cache-20261027');coherent=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
live=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit():continue
 try:
  argv=(p/'cmdline').read_bytes().decode(errors='replace').split('\\0')
  if argv and Path(argv[0]).name in ['lean','cargo','cargo-kani','rustc','cbmc','kissat','cadical'] and str(b) in '\\0'.join(argv):live.append({'pid':p.name,'argv':argv})
 except OSError:pass
assert not live,live
expected=EXPECTED_VALUE;actual={}
for name,pin in expected.items():
 p=b/'NBK_src'/name;got={'sha256':sha(p),'bytes':p.stat().st_size};assert got==pin,(name,got,pin);actual[name]=got
unlisted=[str(p) for n in ['crates','programs'] for p in (b/'NBK_src'/n).rglob('*') if p.is_file() and str(p.relative_to(b/'NBK_src')) not in expected];assert not unlisted,unlisted
cache_end={str(p):{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(cache.rglob('*')) if p.is_file()}
start=START_VALUE
cache_changes=[{'path':p,'before':v,'after':cache_end.get(p)} for p,v in start.items() if cache_end.get(p)!=v]
required_changes=[x for x in cache_changes if Path(x['path']).name.startswith(('NBD_','NBH_'))]
assert not required_changes,('Reused NBD/NBH object changed/missing',required_changes)
lib=json.loads((b/'NBK_LIBRARY_PIN.json').read_text());assert all(sha(Path(p))==v['sha256'] and Path(p).stat().st_size==v['bytes'] for p,v in lib.items())
result={'cache_end':cache_end,'initial_cache_files_unchanged':len(start)-len(cache_changes),'initial_cache_entry_changes_recorded':cache_changes,'reused_NBD_NBH_objects_unchanged':True,'persistent_cache_retained':True,'own_live_provers':live,'frozen_source_and_patch_pins':actual,'library_pins_unchanged':True,'coherent_manifest_pins':{},'tool_file_pins':{},'removed_compiled_solver_scratch':[]}
for name in ['object-source-manifest.json','final-closure-manifest.json','canonical-source-check.json']:
 p=coherent/name
 if p.is_file():result['coherent_manifest_pins'][str(p)]={'sha256':sha(p),'bytes':p.stat().st_size}
for p in [Path('/home/dombarker/.cargo/bin/cargo-kani'),Path('/home/dombarker/.cargo/bin/cargo'),Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')]:
 result['tool_file_pins'][str(p)]={'resolved':str(p.resolve()),'sha256':sha(p),'bytes':p.stat().st_size}
final=b/'NBK_HOST_FINAL.json';final.write_text(json.dumps(result,indent=2)+'\\n')
for name in ['NBK_target','NBK_tmp','.lake']:
 p=b/name
 if p.exists():
  assert p.parent==b and not p.is_symlink()
  files=[f for f in p.rglob('*') if f.is_file()];entry={'path':str(p),'files':len(files),'bytes':sum(f.stat().st_size for f in files)}
  shutil.rmtree(p);result['removed_compiled_solver_scratch'].append(entry);final.write_text(json.dumps(result,indent=2)+'\\n')
print(json.dumps({'source_files':len(actual),'cache_files':len(cache_end),'removed':result['removed_compiled_solver_scratch']}))
'''.replace('B_VALUE',repr(B)).replace('EXPECTED_VALUE',repr(expected)).replace('START_VALUE',repr(json.loads((E/'NBK_CACHE_START.json').read_text())))
r=subprocess.run(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,'python3 -'],input=code,text=True,capture_output=True)
(E/'NBK_FINALIZE_TRANSPORT.json').write_text(json.dumps({'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr,'submitted_once':True},indent=2)+'\n')
# Recover read-only; no second mutation after transport loss.
import importlib.util,sys
sys.argv=['recover','none'];spec=importlib.util.spec_from_file_location('NBK_native',E/'NBK_native.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
rr=m.py('from pathlib import Path; print(Path('+repr(B+'/NBK_HOST_FINAL.json')+').read_text())');assert rr.returncode==0,rr.stderr
out=json.loads(rr.stdout);(E/'NBK_CACHE_END.json').write_text(json.dumps(out.pop('cache_end'),indent=2)+'\n');(E/'NBK_HOST_CLEANUP.json').write_text(json.dumps(out,indent=2)+'\n')
assert r.returncode==0,r.stdout+r.stderr
print(r.stdout)
