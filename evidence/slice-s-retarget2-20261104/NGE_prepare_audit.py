"""Admitted ax2 adaptation: selector/module lists and runtime filenames only."""
from pathlib import Path
import json,re,difflib,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'slice-s-retarget-20261104';J=lambda p:json.loads(p.read_text())
prov=J(E/'NGE_PROVENANCE.json');by={}
for f in sorted(E.glob('NGE_L*/receipt.json')):
 r=J(f)
 if r.get('kind')=='lean' and r['exit_status']==0:by[r['module']]=(f,r)
roots=set(J(P/'NFY_AUDIT_ROOTS.json')['roots']);new={}
for m in ['NGE_'+n for n in prov['order']]:
 f,r=by[m];assert (f.parent/'sources/NGE_generated'/(m+'.lean')).read_bytes()==(E/(m+'.lean')).read_bytes()
 body=next(q['after_body'] for q in prov['files'] if q['target_module']==m)
 suffixes=set(re.findall(r'^(?:protected )?(?:theorem|lemma)\s+([^\s{:(]+)',body,re.M))
 names=set(re.findall(r"^'([^']+)' (?:depends on axioms|does not depend on any axioms)",(f.parent/'stdout.log').read_text(),re.M))
 selected=sorted(n for n in names if not n.startswith('_private.') and (n.rsplit('.',1)[-1] in suffixes or n in suffixes))
 assert selected,m
 new[m]=selected;roots.update(selected)
# Every available historical selected name also gets a direct raw root.
modules=set(json.loads(l)['module'] for l in (P/'NFY_LOADED_scan.jsonl').read_text().splitlines())|set(new)
for row in J(E/'NGE_CERTIFICATES.json')['rows']:
 for q in row['theorems']:
  if q['canonical_module'] in modules:roots.add(q['canonical_name'])
roots=sorted(roots);mods=['NFY_COMBINED_IMPORT']+list(new)
(E/'NGE_TOP_ROOTS.json').write_text(json.dumps(dict(modules=new,roots=sorted({n for ns in new.values() for n in ns})),indent=1)+'\n')
(E/'NGE_COMBINED_IMPORT.lean').write_text(''.join('import '+m+'\n' for m in mods)+'\n#print axioms AspisR1.RPx_Deployed.deployed\n')
# One group per own scope; 64 roots is the admitted NFY raw grouping size.
groups=[roots[i:i+64] for i in range(0,len(roots),64)]
(E/'NGE_AUDIT_ROOTS.json').write_text(json.dumps(dict(headline='AspisR1.RPx_Deployed.deployed',imports=mods,roots=roots,groups=groups),indent=1)+'\n')
for name in ['ProofDriver','Driver']:
 src=(P/('NFY_'+name+'.lean')).read_text();text=src.replace('NFY_COMBINED_IMPORT','NGE_COMBINED_IMPORT').replace('NFY_AUDIT_ROOTS','NGE_AUDIT_ROOTS').replace('NFY_EXPECTED_IMPORTS','NGE_EXPECTED_IMPORTS').replace('NFY_LOADED_scan','NGE_LOADED_scan')
 (E/('NGE_'+name+'.lean')).write_text(text);(E/('NGE_'+name+'.diff')).write_text(''.join(difflib.unified_diff(src.splitlines(True),text.splitlines(True),fromfile='NFY_'+name+'.lean',tofile='NGE_'+name+'.lean')))
 prefix=src.split('  let (modules, roots)')[0];assert text.startswith(prefix)
tables={q['module']:q['imports'] for q in map(json.loads,(P/'NFY_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
for f in E.glob('NGE_*.lean'):tables[f.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',f.read_text(),re.M)))
(E/'NGE_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=im))+'\n' for m,im in sorted(tables.items())))
text=(P/'NFY_batch.py').read_text().replace('NFY_','NGE_')
text=text.replace("elif mode in ['fixtures','scan']:","elif mode.startswith('proof'):jobs=[(mode,['NGE_native/NGE_ProofDriver',mode])]\nelif mode in ['fixtures','scan']:")
(E/'NGE_batch.py').write_text(text)
print(json.dumps(dict(roots=len(roots),new_roots=sum(map(len,new.values())),groups=len(groups))))
