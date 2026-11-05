from pathlib import Path
import json,hashlib,difflib,re
E=Path(__file__).resolve().parent;P=E.parent
roots=['NHH_Embedding.'+n for n in ['base','inherent','complex','quadratic','wide','word_spec','canonical','same_canonical_word','accumulation']]+['AspisR1.RPx_Deployed.deployed']
(E/'NHH_AUDIT_ROOTS.json').write_text(json.dumps({'roots':roots},indent=1)+'\n')
(E/'NHH_COMBINED_IMPORT.lean').write_text('import NGK_COMBINED_IMPORT\nimport NHH_Embedding\n#print axioms AspisR1.RPx_Deployed.deployed\n')
orig=(P/'slice-d-field3-20261105/NGH_Driver.lean').read_text();s=orig
start=s.index('    else if mode == "scan"');end=s.index('    else (#[], #[])',start)
block='    else if mode == "scan" then (#[`NHH_COMBINED_IMPORT], #[])\n'
for i in range((len(roots)+4)//5):block+=f'    else if mode == "proof{i}" then\n      (#[`NHH_COMBINED_IMPORT], #['+', '.join('`'+r for r in roots[5*i:5*i+5])+'])\n'
s=s[:start]+block+s[end:];s=s.replace('NGH_EXPECTED_IMPORTS','NHH_EXPECTED_IMPORTS').replace('NGH_LOADED_scan','NHH_LOADED_scan')
(E/'NHH_Driver.lean').write_text(s)
(E/'NHH_DRIVER.diff').write_text(''.join(difflib.unified_diff(orig.splitlines(True),s.splitlines(True),fromfile='NGH_Driver.lean',tofile='NHH_Driver.lean')))
walker=(P/'slice-d-field3-20261105/NGH_WALKER_SOURCE.lean.txt').read_bytes();assert walker==(P/'axaudit2-20261102/NEP_WALKER.lean').read_bytes()
(E/'NHH_WALKER_PIN.json').write_text(json.dumps({'source':'evidence/axaudit2-20261102/NEP_WALKER.lean','sha256':hashlib.sha256(walker).hexdigest(),'byte_identical':True},indent=1)+'\n')
expected={}
for p in [P/'pool-retarget-20261105/NGK_EXPECTED_IMPORTS.jsonl',P/'slice-d-field3-20261105/NGH_EXPECTED_IMPORTS.jsonl',P/'slice-q-accum-20261104/NFS_EXPECTED_IMPORTS.jsonl']:
 for l in p.read_text().splitlines():
  x=json.loads(l);expected.setdefault(x['module'],x)
for name in ['NHH_Embedding','NHH_COMBINED_IMPORT']:
 imports=['Init']+[n for l in (E/(name+'.lean')).read_text().splitlines() if l.startswith('import ') for n in l[7:].split()];expected[name]=dict(module=name,imports=list(dict.fromkeys(imports)))
(E/'NHH_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(x)+'\n' for _,x in sorted(expected.items())))
s=(P/'slice-d-field3-20261105/NGH_review_batch.py').read_text().replace('NGH_','NHH_').replace('NHH_review_resume','NHH_review')
(E/'NHH_review_batch.py').write_text(s)
