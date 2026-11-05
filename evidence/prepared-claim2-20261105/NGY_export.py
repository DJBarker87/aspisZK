"""Export only own reusable objects; pin full resolved closure and keep cache small."""
from pathlib import Path
import json,hashlib,shutil,lzma,subprocess,re
B=Path(__file__).resolve().parent;assert B.name=='codex-cx-prepared-claim2-20261105'
C=Path('/home/dombarker/project-offloads/codex-cx-prepared-claim-cache-20261104');dst=C/'NGY_exports_20261105';dst.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();exports=[]
for p in (B/'NGY_objects').iterdir():
 if not p.is_file():continue
 q=dst/p.name
 if q.exists():assert sha(p)==sha(q)
 else:shutil.copy2(p,q)
 exports.append(dict(source=str(p),path=str(q),sha256=sha(q),bytes=q.stat().st_size))
configs=[]
for p in B.glob('NGY_L*.json'):
 if not re.fullmatch(r'NGY_L[0-9]{3}\.json',p.name):continue
 x=json.loads(p.read_text());receipt=B/x['attempt']/'receipt.json'
 if x.get('module')=='NGY_COMBINED_IMPORT' and receipt.exists() and json.loads(receipt.read_text())['exit_status']==0:configs.append((x['attempt'],x))
assert configs
_,cfg=max(configs);roots=list(dict.fromkeys([str(dst)]+[p for p in cfg['env']['LEAN_PATH'].split(':') if p!=str(B/'NGY_objects')]))
modules=[json.loads(l)['module'] for l in (B/'NGY_LOADED_scan.jsonl').read_text().splitlines()];pins=[];rels=set(n.replace('.','/')+'.olean' for n in modules)
# Also pin every Aeneas library/sidecar actually resolved through this search path.
for root in roots:
 for stem in ['Aeneas','AeneasMeta']:
  p=Path(root)/stem
  if p.is_dir():rels.update(str(z.relative_to(root)) for z in p.rglob('*.olean'))
for rel in sorted(rels):
 p=next((Path(r)/rel for r in roots if (Path(r)/rel).is_file()),None);assert p,rel
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():pins.append(dict(path=str(z),sha256=sha(z),bytes=z.stat().st_size))
raw=json.dumps(dict(LEAN_PATH=roots,selected_objects=pins)).encode();(B/'NGY_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NGY_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
tool_paths=['/home/dombarker/.cargo/bin/cargo-kani','/home/dombarker/.cargo/bin/cargo','/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/leanc']
tools=[dict(path=p,resolved=str(Path(p).resolve()),sha256=sha(Path(p))) for p in tool_paths]
versions={p:subprocess.check_output([p,'--version'],text=True,stderr=subprocess.STDOUT).strip() for p in [tool_paths[0],tool_paths[2]]}
# All own provers are terminal. Solver temps are under the own TMPDIR; no other job is touched.
removed=[]
for n in ['NGY_target','NGY_native','NGY_objects','NGY_tmp']:
 p=B/n
 if p.exists():shutil.rmtree(p);removed.append(str(p))
report=dict(cache_retained=str(C),exports=exports,selected_closure_objects=len(pins),closure_sha256=hashlib.sha256(raw).hexdigest(),tools=tools,versions=versions,removed_own_build_outputs=removed,cache_size=subprocess.check_output(['du','-sh',str(C)],text=True),export_size=subprocess.check_output(['du','-sh',str(dst)],text=True),disk=subprocess.check_output(['df','-h',str(C)],text=True),audit_binaries='pins/source retained, rebuildable binaries not duplicated in cache',keys_created_or_deleted=False)
(B/'NGY_EXPORT.json').write_text(json.dumps(report,indent=1)+'\n');print(json.dumps(dict(exports=len(exports),closure_objects=len(pins),cache_size=report['cache_size'],export_size=report['export_size'],removed=removed)))
