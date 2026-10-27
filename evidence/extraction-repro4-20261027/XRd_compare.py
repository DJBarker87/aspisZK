"""Complete text inventory of selector-only four-leaf release output vs cohort."""
from pathlib import Path
import json,re,hashlib,difflib
B=Path(__file__).resolve().parent;R=B.parents[1]
s=(R/'evidence/extraction-repro2-20261027/XRb_compare.py').read_text()
exec(s[s.index('def digest'):s.index('inv={')])
old=json.loads((R/'evidence/extraction-repro3-20261027/XRc_cohort_inventory.json').read_text())['inputs']
comparisons={}
for kind in ['Types','Funs']:
 p=B/f'XRd_release_{kind}.lean.txt'
 fresh=declarations(p);cohort=old['cohort_'+kind]['declarations']
 rows=[]
 # Match exact declaration spellings only; namespace/carrier renamings need proof.
 for n in sorted(set(fresh)|set(cohort)):
  a=cohort.get(n);b=fresh.get(n)
  status='release_only' if a is None else 'cohort_only' if b is None else 'same_normalized_text' if a['normalized_sha256']==b['normalized_sha256'] else 'different_normalized_text'
  rows.append({'name':n,'status':status,'cohort':a,'release':{k:v for k,v in b.items() if k!='text'} if b else None,'association':'UNPROVED; exact same-name text matching is not typed transport'})
 comparisons[kind]={'release_path':str(p.relative_to(R)),'release_sha256':digest(p.read_bytes()),'release_bytes':p.stat().st_size,'release_declarations':len(fresh),'cohort_declarations':len(cohort),'counts':{v:sum(r['status']==v for r in rows) for v in ['cohort_only','release_only','same_normalized_text','different_normalized_text']},'declarations':rows}
 c=R/old['cohort_'+kind]['path']
 (B/f'XRd_release_{kind}__cohort.diff').write_text(''.join(difflib.unified_diff(p.read_text().splitlines(True),c.read_text().splitlines(True),fromfile='release four-leaf output',tofile='selected cohort')))
(B/'XRd_declaration_diff.json').write_text(json.dumps({'status':'Selector-only release extraction; check XRd_kit.json for exact coverage','opaque_leaves':['compact::check_values','verifier::echeck','compact::expand_values','candidate::wide_view'],'normalization':'remove comments/attributes/whitespace; compare identical declaration names; no namespace/type/effect equality inference','comparisons':comparisons},indent=2)+'\n')
print({k:v['counts'] for k,v in comparisons.items()})
