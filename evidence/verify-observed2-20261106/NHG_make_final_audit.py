from pathlib import Path
import json,subprocess,re,hashlib
E=Path(__file__).resolve().parent;R=E.parent.parent;revision='4596cd288cd'
def old(n):return subprocess.check_output(['git','show',revision+':'+str((E/n).relative_to(R))],cwd=R)
roots=['AspisR1.NHG_ClaimsDomain.'+n for n in re.findall(r'^theorem (\w+)',(E/'NHG_ClaimsDomain.lean').read_text(),re.M)]
x=json.loads(old('NHG_AUDIT_ROOTS.json'));assert len(x['groups'])==11 and len(roots)==5;x['groups'].append(roots);(E/'NHG_AUDIT_ROOTS.json').write_text(json.dumps(x,indent=1)+'\n')
base=old('NHG_COMBINED_IMPORT.lean').decode();imports=''.join(l+'\n'for l in base.splitlines()if l.startswith('import '));(E/'NHG_COMBINED_IMPORT.lean').write_text(imports+'import NHG_ClaimsDomain\n'+''.join('#print axioms '+r+'\n'for g in x['groups']for r in g))
rows=[json.loads(l)for l in old('NHG_EXPECTED_IMPORTS.jsonl').splitlines()];rows=[r for r in rows if r['module']!='NHG_COMBINED_IMPORT']
for m in ['NHG_ClaimsDomain','NHG_COMBINED_IMPORT']:rows.append(dict(module=m,imports=['Init']+re.findall(r'^import (\S+)',(E/(m+'.lean')).read_text(),re.M)))
(E/'NHG_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(r)+'\n'for r in rows))
files={n:dict(sha256=hashlib.sha256(old(n)).hexdigest(),bytes=len(old(n)))for n in ['NHG_stage4_validate.py','NHG_STAGE4_VALIDATION.json','NHG_STAGE4_MUTATIONS.json','NHG_CLOSED.json','NHG_LEDGER_DELTA.json','NHG_COMBINED_IMPORT.lean','NHG_AUDIT_ROOTS.json','NHG_EXPECTED_IMPORTS.jsonl']}
(E/'NHG_STAGE4_SEAL.json').write_text(json.dumps(dict(revision=subprocess.check_output(['git','rev-parse',revision],cwd=R,text=True).strip(),files=files),indent=1)+'\n')
(E/'NHG_FINAL_ROOTS.json').write_text(json.dumps(dict(roots=roots,batch=11,support_only=True,closed_rows_added=0),indent=1)+'\n')
print('Five additional support roots; no row promotion')
