"""Read-only archival of owned results; binaries are represented by hash/size."""
from pathlib import Path
import difflib,hashlib,json,shutil
H=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023');D=H/'native-drop';O=D/'packet';O.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def copy(p,q):
 q.parent.mkdir(parents=True,exist_ok=True)
 if p.suffix=='.json' and p.stat().st_size>5_000_000:
  q.with_suffix(q.suffix+'.metadata.json').write_text(json.dumps(dict(sha256=sha(p),bytes=p.stat().st_size))+'\n')
 else:shutil.copyfile(p,q)
for p in (D/'lean').iterdir():
 if p.is_file():copy(p,O/'lean'/p.name)
final=(D/'backend/base/src/PrePasses.ml').read_text()
strip='''{f with src = TopLevelItem; item_meta = {f.item_meta with name =
      List.filter (function PeImpl _ -> false | _ -> true) f.item_meta.name}}'''
for a in range(8,13):
 B=D/'backend'/f'prover-rw-native-drop-build-{a:03d}';E=O/'backend'/B.name
 for p in B.iterdir():
  if p.is_file() and p.name!='go':copy(p,E/p.name)
 pre=json.loads((B/'preflight.json').read_text())
 s=final
 if a in [8,9,10]:s=s.replace(strip,'{f with src = TopLevelItem}')
 if a in [8,9]:s=s.replace('let id (p : place) = match p.kind','let id p = match p.kind')
 if a==11:s=s.replace('function PeImpl _','function Impl _')
 assert hashlib.sha256(s.encode()).hexdigest()==pre['candidate_source_sha256']['src/PrePasses.ml'],a
 (E/'PrePasses.ml.txt').write_text(s)
 p=D/'backend/base/src/Main.ml';assert sha(p)==pre['candidate_source_sha256']['src/Main.ml'];copy(p,E/'Main.ml.txt')
for name in ['base-provenance.json','dependency-manifest.json']:
 copy(D/'backend'/name,O/'backend'/name)
for a in range(25,36):
 B=D/f'extraction{a:03d}'
 for p in B.rglob('*'):
  if p.is_file():
   q=O/B.name/p.relative_to(B)
   if q.suffix=='.lean':q=q.with_suffix('.lean.txt')
   copy(p,q)
for name in ['ProverRwNativeDropNoDrop.llbc','ProverRwNativeDropescape.llbc']:
 copy(D/name,O/'inputs'/name)
copy(H/'src/tools/prover-rw-20261023/native-drop/fixtures/Cargo.lock',O/'inputs/fixtures-Cargo.lock')
p=D/'backend/base/src/Config.ml'
provenance=json.loads((D/'backend/base-provenance.json').read_text())
old=provenance['source_manifest']['src/Config.ml']['sha256']
assert sha(p)==old
(O/'default-assessment.json').write_text(json.dumps(dict(config_sha256=sha(p),matches_reused_baseline_source_manifest=True,default='drop_as_no_op = ref true',explicit_switch='-eval-drops',prior_receipt_false_labels='Unsupported: prior baseline commands020/022 omit -eval-drops. Source Drop branch ignoring fn_ptr is separate static evidence; prior commands do not show drop_value branch execution.'),indent=2)+'\n')
for name in ['Main.ml','PrePasses.ml']:
 old=(H/'rng-extractor/base/src'/name).read_text().splitlines(True)
 new=(D/'backend/base/src'/name).read_text().splitlines(True)
 (O/('candidate012-'+name+'.diff')).write_text(''.join(difflib.unified_diff(old,new,fromfile='candidate007/'+name,tofile='candidate012/'+name)))
print(O)
