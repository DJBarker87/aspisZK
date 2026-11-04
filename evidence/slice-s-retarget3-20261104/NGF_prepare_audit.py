"""Only admitted driver selections/runtime filenames change; walker unchanged."""
from pathlib import Path
import json,re,hashlib,difflib,sys
E=Path(__file__).resolve().parent;R=E.parents[1];P=E.parent/'slice-s-retarget-20261104'
J=lambda p:json.loads(p.read_text());H=lambda b:hashlib.sha256(b).hexdigest()
p=J(E/'NGF_PROVENANCE.json');base=J(P/'NFY_AUDIT_ROOTS.json');roots=set(base['roots']);mods=['NFY_COMBINED_IMPORT']+[r['target_module'] for r in p['files']];top={}
for m in mods[1:]:
 rs=[f for f in sorted(E.glob('NGF_L*/receipt.json')) if (lambda j:j['kind']=='lean' and j['module']==m and j['exit_status']==0)(J(f))]
 assert rs,m
 f=rs[-1];assert (f.parent/'sources/NGF_generated'/(m+'.lean')).read_bytes()==(E/(m+'.lean')).read_bytes()
 names=set(re.findall(r"^'([^']+)' (?:depends on axioms|does not depend on any axioms)",(f.parent/'stdout.log').read_text(),re.M));names={n for n in names if not n.startswith('_private.')};top[m]=sorted(names);roots.update(names)
# Complete certificate inventory, regardless of root graph. Only declarations
# whose exact module is in the coherent candidate are added to raw root list.
loaded={r['module'] for r in map(json.loads,(P/'NFY_LOADED_scan.jsonl').read_text().splitlines())}|set(mods)
old={t['legacy_name']:t['canonical_module'] for row in J(P/'NFY_CERTIFICATES.json')['rows'] for t in row['canonical_theorem_associations']}
for row in J(E/'NGF_CERT_INVENTORY.json'):
 for t in row['theorems']:
  prior=old.get(t['legacy_name'],'');m=p['module_owner'].get(prior,prior)
  if m in loaded:roots.add(t['canonical_name'])
roots=sorted(roots)
# One raw partition per remaining slot, after combined/drivers/link/fixtures/scan.
used=max(int(f.name[5:8]) for f in E.glob('NGF_L[0-9][0-9][0-9].json'))
partitions=110-used-7
assert partitions>0
# Output root partitions only after source builds; repartitioning is not replay.
groups=[roots[i*len(roots)//partitions:(i+1)*len(roots)//partitions] for i in range(partitions)]
(E/'NGF_TOP_ROOTS.json').write_text(json.dumps(dict(modules=top,roots=sorted({n for ns in top.values() for n in ns})),indent=1)+'\n')
(E/'NGF_COMBINED_IMPORT.lean').write_text(''.join('import '+m+'\n' for m in mods)+ '#print axioms AspisR1.RPx_Deployed.deployed\n'+''.join('#print axioms '+n+'\n' for n in sorted({n for ns in top.values() for n in ns})))
(E/'NGF_AUDIT_ROOTS.json').write_text(json.dumps(dict(headline=base['headline'],imports=mods,roots=roots,groups=groups),indent=1)+'\n')
for name in ['ProofDriver','Driver']:
 source=(P/('NFY_'+name+'.lean')).read_text();text=source.replace('NFY_COMBINED_IMPORT','NGF_COMBINED_IMPORT').replace('NFY_AUDIT_ROOTS','NGF_AUDIT_ROOTS').replace('NFY_EXPECTED_IMPORTS','NGF_EXPECTED_IMPORTS').replace('NFY_LOADED_scan','NGF_LOADED_scan')
 (E/('NGF_'+name+'.lean')).write_text(text)
 (E/('NGF_'+name.upper()+'.diff')).write_text(''.join(difflib.unified_diff(source.splitlines(True),text.splitlines(True),fromfile='NFY_'+name+'.lean',tofile='NGF_'+name+'.lean')))
tables={r['module']:r['imports'] for r in map(json.loads,(P/'NFY_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
for n,r in J(E/'NGF_SOURCE_GRAPH.json').items():
 tables[n]=list(dict.fromkeys(['Init']+r['imports']))
for r in p['files']:
 tables[r['source_module']]=list(dict.fromkeys(['Init']+r['imports_before']))
for f in E.glob('NGF_*.lean'):tables[f.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',f.read_text(),re.M)))
(E/'NGF_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=n,imports=v))+'\n' for n,v in sorted(tables.items())))
s=(P/'NFY_batch.py').read_text().replace('NFY_','NGF_').replace('batch*15,min((batch+1)*15','batch,min(batch+1')
(E/'NGF_batch.py').write_text(s)
walker=(R/'evidence/axaudit2-20261102/NEP_WALKER.lean').read_bytes();snapshot=(P/'NFY_WALKER_SOURCE.lean').read_bytes();assert walker==snapshot
(E/'NGF_WALKER_SOURCE.lean').write_bytes(walker)
x=J(P/'NFY_WALKER_CONFORMANCE.json');x.update(source_sha256=H(walker),byte_identical=True,source_snapshot='NGF_WALKER_SOURCE.lean',actual_object=dict(x['actual_object'],path=x['actual_object']['path'].replace('codex-cx-slice-s-retarget-cache-','codex-cx-slice-s-retarget3-cache-')),reuse='Exact copied object, source and accepted predecessor receipts, plus own same-binary fixture replay required')
(E/'NGF_WALKER_CONFORMANCE.json').write_text(json.dumps(x,indent=1)+'\n')
print(json.dumps(dict(roots=len(roots),groups=len(groups),used=used,planned_total=used+7+len(groups))))
