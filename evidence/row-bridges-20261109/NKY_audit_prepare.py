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
roots=[]
for n in mods:
 s=(E/(n+'.lean')).read_text();namespace=re.search(r'^namespace ([\w.]+)',s,re.M)[1]
 roots += [namespace+'.'+n for n in re.findall(r'^theorem (\w+)',s,re.M)]
# Full predecessor root set plus all new roots, each in this combined environment.
old=json.loads((P/'NKW_AUDIT_ROOTS.json').read_text());prior=[n for g in old['groups']for n in g]
allroots=list(dict.fromkeys(prior+roots));groups=[allroots[i:i+360]for i in range(0,len(allroots),360)]
(E/'NKY_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=groups,predecessor_roots=len(set(prior)),new_roots=roots,total=len(allroots)),indent=1)+'\n')
(E/'NKY_AUDIT_MODULES.json').write_text(json.dumps([['NKY_COMBINED_IMPORT']for _ in groups],indent=1)+'\n')
expected=[json.loads(l)for l in(P/'NKW_EXPECTED_IMPORTS.jsonl').read_text().splitlines()]
for n in mods+['NKY_COMBINED_IMPORT']:
 s=(E/(n+'.lean')).read_text();expected.append(dict(module=n,imports=['Init']+re.findall(r'^import ([\w.]+)',s,re.M)))
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
