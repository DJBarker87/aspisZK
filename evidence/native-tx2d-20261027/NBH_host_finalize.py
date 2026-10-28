"""Own terminal validation/cleanup. One submission; recover read-only after transport loss."""
from pathlib import Path
import subprocess,json,sys,hashlib,importlib.util,time
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-native-tx2d-20261027';REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
assert len(list(E.glob('NBH_K*/receipt.json')))==30
for p in E.glob('NBH_K*/receipt.json'):
 q=json.loads((E/(p.parent.name+'-graph.json')).read_text());assert q['lock_unchanged'] and q['graph_matches_frozen']
# Pin every frozen crate/program source, plus the frozen lock. No large corpus copy.
rows=subprocess.check_output(['git','ls-tree','-r',REV,'--','crates','programs','Cargo.lock'],text=True).splitlines()
pins={}
for row in rows:
 meta,path=row.split('\t',1)
 if meta.split()[1]!='blob':continue
 data=subprocess.check_output(['git','cat-file','blob',meta.split()[2]])
 pins[path]={'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
x=json.loads((E/'NBH_SYNC005-payload.json').read_text())
expected=dict(pins)
for path,v in x['parents'].items():
 data=(v['original']+v['marker']).encode();expected[path]={'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
for path,v in x['files'].items():
 data=v.encode();expected[path]={'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
code=r'''
from pathlib import Path
import hashlib,json,os,shutil
b=Path('/home/dombarker/project-offloads/codex-cx-native-tx2d-20261027');c=Path('/home/dombarker/project-offloads/codex-cx-leaf-cache-20261027');coherent=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
expected=EXPECTED
# Inspect exact executable names; the current audit command cannot match itself.
live=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit():continue
 try:
  args=(p/'cmdline').read_bytes().decode(errors='replace').split('\0')
  if args and Path(args[0]).name in ['lean','cargo','cargo-kani','rustc','cbmc','kissat','cadical'] and str(b) in '\0'.join(args):live.append({'pid':p.name,'argv':args})
 except (OSError,ProcessLookupError):pass
assert not live,live
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
actual={}
for name,pin in expected.items():
 p=b/'NBH_src'/name
 got={'sha256':sha(p),'bytes':p.stat().st_size};assert got==pin,(name,got,pin);actual[name]=got
unlisted=[]
for prefix in ['crates','programs']:
 for p in (b/'NBH_src'/prefix).rglob('*'):
  if p.is_file() and str(p.relative_to(b/'NBH_src')) not in expected:unlisted.append(str(p))
assert not unlisted,unlisted
cache={str(p):{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(c.rglob('*')) if p.is_file()}
lib=json.loads((b/'NBH_LIBRARY_PIN.json').read_text());assert all(sha(Path(p))==v['sha256'] and Path(p).stat().st_size==v['bytes'] for p,v in lib.items())
manifest_names=['object-source-manifest.json','final-closure-manifest.json','canonical-source-check.json']
manifest_pins={str(coherent/n):{'sha256':sha(coherent/n),'bytes':(coherent/n).stat().st_size} for n in manifest_names if (coherent/n).is_file()}
tools={}
for p in [Path('/home/dombarker/.cargo/bin/cargo-kani'),Path('/home/dombarker/.cargo/bin/cargo')]:
 if p.exists():tools[str(p)]={'resolved':str(p.resolve()),'sha256':sha(p),'bytes':p.stat().st_size}
result={'cache_end':cache,'frozen_source_and_patch_pins':actual,'library_pins_unchanged':True,'coherent_manifest_pins':manifest_pins,'tool_file_pins':tools,'own_live_provers':live,'persistent_cache_retained':True,'source_scratch_retained':True,'removed_compiled_solver_scratch':[]}
out=b/'NBH_HOST_FINAL.json'
out.write_text(json.dumps(result,indent=2)+'\n')
for name in ['NBH_target','NBH_tmp']:
 p=b/name
 if p.exists():
  assert p.parent==b and not p.is_symlink()
  files=[f for f in p.rglob('*') if f.is_file()]
  entry={'path':str(p),'files':len(files),'bytes':sum(f.stat().st_size for f in files)}
  shutil.rmtree(p);result['removed_compiled_solver_scratch'].append(entry)
  out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'source_files':len(actual),'cache_files':len(cache),'removed':result['removed_compiled_solver_scratch']}))
'''.replace('EXPECTED',repr(expected))
# Input via stdin avoids large shell arguments. Do not resubmit after submission.
r=subprocess.run(['ssh','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,'python3 -'],input=code,capture_output=True,text=True)
(E/'NBH_FINALIZE_TRANSPORT.json').write_text(json.dumps({'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr,'submitted_once':True},indent=2)+'\n')
if r.returncode==255:time.sleep(60)
# Use the existing own transport recovery, read-only; never rerun cleanup.
sys.argv=['recover','none'];sp=importlib.util.spec_from_file_location('NBH_native',E/'NBH_native.py');m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
rr=m.py("from pathlib import Path; print(Path('/home/dombarker/project-offloads/codex-cx-native-tx2d-20261027/NBH_HOST_FINAL.json').read_text())")
assert rr.returncode==0,rr.stderr
result=json.loads(rr.stdout)
(E/'NBH_CACHE_END.json').write_text(json.dumps(result.pop('cache_end'),indent=2)+'\n')
(E/'NBH_HOST_CLEANUP.json').write_text(json.dumps(result,indent=2)+'\n')
assert r.returncode==0,r.stdout+r.stderr
print('host terminal; sources/library pinned; own compiled and solver scratch removed; persistent cache retained')
