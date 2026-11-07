"""Build one full ledger23 + NLQ + NMB audit; no source-name lookup of helpers."""
from pathlib import Path
import json,re,hashlib,lzma
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[json.loads(x)for x in (E/'NMB_ATTEMPTS.jsonl').read_text().splitlines()]
valid={}
for r in receipts:
 m=r.get('module','');p=E/(m+'.lean')
 if r.get('kind')=='lean' and r.get('exit_status')==0 and p.exists() and sha(p) in r.get('source_hashes',{}).values():valid[m]=(r,p)
valid={m:v for m,v in valid.items() if not any(x in m for x in ['Inspect','Driver','COMBINED_IMPORT'])}
modules=sorted(valid)
imports=['NLS_COMBINED_IMPORT','NLQ_COMBINED_IMPORT','NLD_COMBINED_IMPORT','NLF_SdkBorrowLaw']+modules
base=json.loads((E.parent/'ledger23-20261110/NLS_AUDIT_ROOTS.json').read_text())
roots=list(base['roots'])
q=json.loads((E.parent/'tx1-entry2-20261110/NLQ_AUDIT_ROOTS.json').read_text())
roots+=q['roots'];new=[]
for m,(r,p)in valid.items():
 log=lzma.decompress((E/r['attempt']/'stdout.log.xz').read_bytes()).decode()
 for n in re.findall(r"^'([^']+)' (?:depends on axioms|does not depend on any axioms)",log,re.M):
  if n not in roots:new.append(n)
  roots.append(n)
roots=list(dict.fromkeys(roots+['AspisR1.RPx_Deployed.deployed','AspisR1.NKR_ScheduleExt.transition','NHC_DecodeModel.decoder_error']))
# At most 220 roots per 180s scope; full replay is performed once.
groups=[roots[i:i+220]for i in range(0,len(roots),220)]
(E/'NMB_COMBINED_IMPORT.lean').write_text(''.join('import '+m+'\n'for m in imports)+'#check @AspisR1.RPx_Deployed.deployed\n#print axioms AspisR1.RPx_Deployed.deployed\n'+''.join('#check @'+r+'\n'for r in new))
(E/'NMB_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=groups),indent=1)+'\n')
(E/'NMB_AUDIT_MODULES.json').write_text(json.dumps([['NMB_COMBINED_IMPORT']for _ in groups])+'\n')
expected={}
for f in [E.parent/'ledger23-20261110/NLS_EXPECTED_IMPORTS.jsonl',E.parent/'tx1-entry2-20261110/NLQ_EXPECTED_IMPORTS.jsonl',E.parent/'tx1-entry-20261109/NLD_EXPECTED_IMPORTS.jsonl',E.parent/'sdk-borrow-20261109/NLF_EXPECTED_IMPORTS.jsonl']:
 for l in f.read_text().splitlines():
  r=json.loads(l);m=r['module']
  if m in expected:assert expected[m]==r,(m,f)
  expected[m]=r
for m,(r,p)in valid.items():expected[m]=dict(module=m,imports=list(dict.fromkeys(['Init']+re.findall(r'^import (\S+)',p.read_text(),re.M))))
expected['NMB_COMBINED_IMPORT']=dict(module='NMB_COMBINED_IMPORT',imports=['Init']+imports)
(E/'NMB_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(expected[m])+'\n'for m in sorted(expected)))
plan=dict(modules=modules,new_roots=new,root_count=len(roots),group_count=len(groups),baseline='ledger23 NLO580/0/19',baseline_pin=sha(E.parent/'ledger23-20261110/NLO_COMBINED_IMPORT.lean'),raw_replay='One full combined raw ax2 walk; source intermediates only, no row root')
(E/'NMB_AUDIT_PLAN.json').write_text(json.dumps(plan,indent=1)+'\n')
print(json.dumps(dict(modules=len(modules),roots=len(roots),groups=len(groups))))
