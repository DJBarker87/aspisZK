from pathlib import Path
import json,re,subprocess,hashlib
E=Path(__file__).resolve().parent;R=E.parent.parent;revision='ed0fb939429'
def old(n):return subprocess.check_output(['git','show',revision+':'+str((E/n).relative_to(R))],cwd=R)
modules=['NHG_FinishLeaves','NHG_SelectedClaim','NHG_AddWords','NHG_ExtraLeaves']
roots=['AspisR1.'+m+'.'+n for m in modules for n in re.findall(r'^theorem (\w+)',(E/(m+'.lean')).read_text(),re.M)]
prior=json.loads(old('NHG_AUDIT_ROOTS.json'));assert len(prior['groups'])==8
prior['groups'] += [roots[i:i+12]for i in range(0,len(roots),12)]
(E/'NHG_AUDIT_ROOTS.json').write_text(json.dumps(prior,indent=1)+'\n')
imports=''.join(l+'\n'for l in old('NHG_COMBINED_IMPORT.lean').decode().splitlines()if l.startswith('import '))
(E/'NHG_COMBINED_IMPORT.lean').write_text(imports+''.join('import '+m+'\n'for m in modules)+''.join('#print axioms '+r+'\n'for g in prior['groups']for r in g))
rows=list(map(json.loads,old('NHG_EXPECTED_IMPORTS.jsonl').splitlines()));rows=[r for r in rows if r['module']!='NHG_COMBINED_IMPORT']
for m in modules+['NHG_COMBINED_IMPORT']:
 assert not any(r['module']==m for r in rows)
 rows.append(dict(module=m,imports=['Init']+re.findall(r'^import (\S+)',(E/(m+'.lean')).read_text(),re.M)))
(E/'NHG_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(r)+'\n'for r in rows))
seal={n:dict(sha256=hashlib.sha256(old(n)).hexdigest(),bytes=len(old(n)))for n in ['NHG_stage3_validate.py','NHG_STAGE3_VALIDATION.json','NHG_STAGE3_MUTATIONS.json','NHG_CLOSED.json','NHG_LEDGER_DELTA.json','NHG_COMBINED_IMPORT.lean','NHG_AUDIT_ROOTS.json','NHG_EXPECTED_IMPORTS.jsonl']}
(E/'NHG_STAGE3_SEAL.json').write_text(json.dumps(dict(revision=subprocess.check_output(['git','rev-parse',revision],cwd=R,text=True).strip(),files=seal,retained_checks='All historical checks and their inputs/results remain immutable in this git revision. Stage4 only adds admission checks.'),indent=1)+'\n')
(E/'NHG_STAGE4_ROOTS.json').write_text(json.dumps(dict(modules=modules,roots=roots,batches=list(range(8,len(prior['groups']))),retained_batches=list(range(8)),headline='AspisR1.RPx_Deployed.deployed'),indent=1)+'\n')
print(len(roots),'new roots;',sum(map(len,prior['groups'])),'total')
