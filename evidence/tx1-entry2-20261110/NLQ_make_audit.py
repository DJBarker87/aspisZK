from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent
receipts=[json.loads(x) for x in (E/'NLQ_ATTEMPTS.jsonl').read_text().splitlines()]
valid={}
for r in receipts:
 m=r.get('module','');s=E/(m+'.lean')
 if not s.exists():s=E/'NLQ_dependency_inputs'/(m+'.lean.txt')
 if r.get('kind')=='lean' and r.get('exit_status')==0 and s.exists() and hashlib.sha256(s.read_bytes()).hexdigest() in r.get('source_hashes',{}).values():valid[m]=(r,s)
valid={m:v for m,v in valid.items() if not any(x in m for x in ['Inspect','Driver','COMBINED_IMPORT'])}
modules=sorted(valid)
imports=['NLO_COMBINED_IMPORT','NLD_COMBINED_IMPORT','NLF_SdkBorrowLaw']+modules
(E/'NLQ_COMBINED_IMPORT.lean').write_text(''.join('import '+m+'\n' for m in imports)+'#check @AspisR1.RPx_Deployed.deployed\n#print axioms AspisR1.RPx_Deployed.deployed\n')
base=json.loads((E.parent/'ledger22-20261110/NLO_AUDIT_ROOTS.json').read_text());roots=list(base['roots']);new=[]
for m,(r,s) in valid.items():
 log=(E/r['attempt']/'stdout.log').read_text()
 for n in re.findall(r"^'([^']+)' (?:depends on axioms|does not depend on any axioms)",log,re.M):
  if n not in roots:new.append(n);roots.append(n)
inherited_count=len(base['roots'])
roots=list(dict.fromkeys(new+['AspisR1.RPx_Deployed.deployed','AspisR1.NKR_ScheduleExt.transition','NHC_DecodeModel.decoder_error']))
groups=[roots[i:i+40]for i in range(0,len(roots),40)]
with (E/'NLQ_COMBINED_IMPORT.lean').open('a') as out:
 for root in new:out.write('#check @'+root+'\n')
(E/'NLQ_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=groups),indent=1)+'\n')
(E/'NLQ_AUDIT_MODULES.json').write_text(json.dumps([['NLQ_COMBINED_IMPORT']for _ in groups])+'\n')
expected={}
for f in [E.parent/'ledger22-20261110/NLO_EXPECTED_IMPORTS.jsonl',E.parent/'tx1-entry-20261109/NLD_EXPECTED_IMPORTS.jsonl',E.parent/'sdk-borrow-20261109/NLF_EXPECTED_IMPORTS.jsonl']:
 if f.exists():
  for line in f.read_text().splitlines():
   r=json.loads(line);m=r['module']
   if m in expected:assert expected[m]==r
   expected[m]=r
for m,(r,s) in valid.items():
 ins=['Init']+re.findall(r'^import (\S+)',s.read_text(),re.M)
 expected[m]=dict(module=m,imports=list(dict.fromkeys(ins)))
expected['NLQ_COMBINED_IMPORT']=dict(module='NLQ_COMBINED_IMPORT',imports=['Init']+imports)
(E/'NLQ_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(expected[m])+'\n'for m in sorted(expected)))
(E/'NLQ_AUDIT_PLAN.json').write_text(json.dumps(dict(modules=modules,new_roots=new,root_count=len(roots),group_count=len(groups),inherited_root_count=inherited_count,inherited_audit='evidence/ledger22-20261110/NLO_AUDIT.json',raw_replay_coverage='Added roots, headline and known collector differences freshly replayed; unchanged ledger22 raw results retained by reference',excluded_failed_or_stale=sorted(set(r.get('module','') for r in receipts if r.get('kind')=='lean')-set(modules))),indent=1)+'\n')
print(json.dumps(dict(valid_modules=len(modules),new_roots=len(new),roots=len(roots),groups=len(groups))))
