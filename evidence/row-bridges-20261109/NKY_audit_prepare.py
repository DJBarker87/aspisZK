from pathlib import Path
import json,re,lzma
E=Path(__file__).resolve().parent;P=E.parent/'ledger20-20261109';B='/home/dombarker/project-offloads/codex-cx-row-bridges-20261109'
for n in ['Driver','ProofDriver']:
 s=(P/('NKW_'+n+'.lean')).read_text().replace('NKW','NKY')
 (E/('NKY_'+n+'.lean')).write_text(s)
(E/'NKY_batch.py').write_text((P/'NKW_batch.py').read_text().replace('NKW','NKY'))
s=(P/'NKW_pin.py').read_text().replace('NKW','NKY').replace('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NKY_20261109/NKY_exports_20261109',B+'/NKY_exports_20261109')
(E/'NKY_pin.py').write_text(s)
mods=['NKY_LevelCarrier','NKY_LevelsLiteral','NKY_LevelsStep','NKY_LevelsBody','NKY_LevelSchedule','NKY_LevelsLoop','NKY_CanonicalLift','NKY_LevelsRoot','NKY_LevelsUnique','NKY_LevelsComplete','NKY_BoxAction','NKY_BoxFrame','NKY_BoxPacket','NKY_BoxRoots','NKY_BoxCarrier','NKY_BoxComplete','NKY_BoxTotal']
def theorem_names(n):
 namespace=None;out=[]
 for line in (E/(n+'.lean')).read_text().splitlines():
  m=re.match(r'namespace ([\w.]+)',line)
  if m:namespace=m[1]
  m=re.match(r'theorem (\w+)',line)
  if m:assert namespace;out.append(namespace+'.'+m[1])
  if line.startswith('end ')and line[4:]==namespace:namespace=None
 return out
roots=[r for n in mods for r in theorem_names(n)]
extra=['NKY_BoxPost','NKY_BoxPostWindows','NKY_BoxSource']
extra_roots=[r for n in extra for r in theorem_names(n)]
old=json.loads((P/'NKW_AUDIT_ROOTS.json').read_text());prior=[n for g in old['groups']for n in g]
base=list(dict.fromkeys(prior+roots));groups=[base[i:i+360]for i in range(0,len(base),360)]
assert len(base)==10585
allroots=base+extra_roots;groups.append(extra_roots)
(E/'NKY_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=groups,predecessor_roots=len(set(prior)),new_roots=roots+extra_roots,total=len(allroots),incremental_group=30,unchanged_prior_groups=30),indent=1)+'\n')
(E/'NKY_AUDIT_MODULES.json').write_text(json.dumps([['NKY_COMBINED_IMPORT']for _ in groups],indent=1)+'\n')
expected=[json.loads(l)for l in(P/'NKW_EXPECTED_IMPORTS.jsonl').read_text().splitlines()]
for n in mods+extra+['NKY_COMBINED_IMPORT']:
 t=(E/(n+'.lean')).read_text();expected.append(dict(module=n,imports=['Init']+re.findall(r'^import ([\w.]+)',t,re.M)))
(E/'NKY_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(r)+'\n'for r in expected))
(E/'NKY_DRIVER_DIFF.md').write_text('''# Audit-driver adaptation

The admitted NKW raw ax2 proof driver and canonical NFX scanner are reused
with NKW path/module prefixes changed to NKY. No traversal, matcher,
recursor/opaque handling, metadata comparison or standard-axiom allowlist is
changed. All predecessor roots and all new roots are selected in the new
combined import environment. The exact walker/memory-limit sources are reused
unchanged; optimized linkage and the eight fidelity fixtures are run here.
''')
# Own runner path repair only, strict predecessor comparison unchanged.
p=E/'NKY_run.py';s=p.read_text().replace("E.parent/'ledger19-20261108/NKN_CLOSURE_PINS.json.xz'","E.parent/'ledger20-20261109/NKW_CLOSURE_PINS.json.xz'")
p.write_text(s)
print('audit inputs prepared:',len(groups),'groups,',len(allroots),'roots')
