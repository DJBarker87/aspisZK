#!/usr/bin/env python3
"""Validate retained receipts and the deliberately narrow copy transformation."""
import hashlib, json, pathlib, re, subprocess
ROOT = pathlib.Path(__file__).resolve().parents[2]
BASE = ROOT/'docs/research/100bit-spend-path-20261013'
E = BASE/'evidence/import-coll-20261021'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = json.loads((E/'manifest.json').read_text())
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
accepted = {}
for r in manifest['attempts']:
 d = E/f"{r['module']}-{r['attempt']}"
 assert sha(d/'source.lean.txt') == r['source_sha256'], d
 assert json.loads((d/'receipt.json').read_text()) == r, d
 for field in ['target','exit','wall_seconds','peak_rss_bytes','swaps','source_revision','deps_fingerprint','axiom_lines','errors']:
  assert field in r, (d,field)
 assert r['peak_rss_bytes'] and r['swaps'] == 0, d
 if r['exit'] == 0:
  assert not r['errors'], d
  for line in r['axiom_lines']:
   m = re.search(r'depends on axioms: \[([^]]*)\]',line)
   if m: assert {a.strip() for a in m[1].split(',')} <= allowed, (d,line)
  accepted[r['module']] = r
for p in (E/'prototype').rglob('*.lean'):
 mod = str(p.relative_to(E/'prototype')).removesuffix('.lean').replace('/','.')
 if mod == 'ImportUnionAllConesBaseline': continue
 assert mod in accepted and accepted[mod]['source_sha256'] == sha(p), mod
 # All public copied theorems have individual audits in their defining file.
 for name in re.findall(r'^theorem (\S+)',p.read_text(),re.M):
  assert any("."+name+"' " in line for line in accepted[mod]['axiom_lines']), (mod,name)
for r in json.loads((E/'copy-provenance.json').read_text()):
 original = ROOT/r['original']; copy = ROOT/r['prototype']
 assert sha(original) == r['original_sha256'], original
 assert sha(copy) == r['prototype_sha256'], copy
 text = copy.read_text()
 if r['module'] in {'AspisR1S3InactiveSource.Types','Stage2ContinuationTypes'}:
  text = text.replace('import ImportUnionNamedDiscriminant\n','').replace('@[import_union_discriminant]','@[discriminant isize]')
 strip = lambda s: '\n'.join(l for l in s.splitlines() if not l.startswith('#print axioms')).strip()
 assert strip(text) == strip(original.read_text()), r['module']
for rel in ['lean/R1FinalSoundnessBinPerQueryR19.lean','lean/R1FinalSoundness.lean']:
 p = BASE/rel
 baseline = subprocess.check_output(['git','show','f01405274:'+str(p.relative_to(ROOT))],cwd=ROOT)
 assert p.read_bytes() == baseline, p
# Raw per-module inventory is authoritative even for duplicate theorem-only modules.
raw = json.loads((E/'raw-inventory.json').read_text())
owners = {}
for name, owner in raw: owners.setdefault(name,set()).add(owner)
expected = {name:sorted(mods) for name,mods in sorted(owners.items()) if len(mods)>1}
assert expected == json.loads((E/'raw-duplicate-declarations.json').read_text())
graph = json.loads((E/'raw-module-graph.json').read_text())
for row in graph: assert sha(pathlib.Path(row['path'])) == row['sha256'], row['module']
closure = {'AspisR1S3InactiveSource.Types','Stage2ContinuationTypes'}
while True:
 old = set(closure)
 for row in graph:
  if closure.intersection(row['imports']): closure.add(row['module'])
 if closure == old: break
assert closure == {r['module'] for r in json.loads((E/'copy-provenance.json').read_text())}
for r in json.loads((E/'private-object-pins.json').read_text()):
 p = pathlib.Path('/tmp/codex-cx-import-coll-20261021-objects')/(r['module'].replace('.','/')+'.olean')
 assert sha(p) == r['sha256'] and p.stat().st_size == r['bytes'], p
changes = subprocess.check_output(['git','diff','--name-status','f01405274'],cwd=ROOT,text=True).splitlines()
assert all(line.startswith('A\t') for line in changes), changes
assert all(line.split('\t')[1].startswith(('tools/import-union/','docs/research/100bit-spend-path-20261013/evidence/import-coll-20261021/','docs/research/100bit-spend-path-20261013/design/IMPORT-UNION-20261021.md')) for line in changes), changes
subprocess.run(['git','diff','--check','f01405274'],cwd=ROOT,check=True)
print(json.dumps({'raw_project_modules':len(graph),'raw_declaration_entries':len(raw),'duplicate_names':len(expected),'rebuilt_dependent_closure':len(closure),'attempts':len(manifest['attempts']),'exit_zero':sum(r['exit']==0 for r in manifest['attempts']),'exit_nonzero':sum(r['exit']!=0 for r in manifest['attempts']),'maximum_rss_bytes':max(r['peak_rss_bytes'] for r in manifest['attempts']),'swaps':0,'all_cone_audits':len(accepted['ImportUnionAllConesCx20261021']['axiom_lines']),'headline_axioms':accepted['ImportUnionHeadlineCx20261021']['axiom_lines'],'existing_files_changed':False},indent=2))
