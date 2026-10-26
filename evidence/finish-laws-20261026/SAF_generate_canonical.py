"""Generate new-prefix consumers for the accepted-only canonicality removal.
No existing source is edited. All source transforms are reviewed in the diff.
"""
from pathlib import Path
import json,re
ROOT=Path(__file__).resolve().parents[2]
E=ROOT/'evidence/finish-laws-20261026'
old=json.loads((E/'SAF_canonical_plan.json').read_text())
rename={m:'SAF_C_'+m for m in old}
for m in old:
 s=(ROOT/'lean'/f'{m}.lean').read_text()
 for a,b in sorted(rename.items(),key=lambda x:-len(x[0])):
  s=re.sub(r'\b'+re.escape(a)+r'\b',b,s)
 # These are the exact eight-operand reverse-decoder assumptions, not wire scans.
 s=re.sub(r'    \(canonical_S3_S4_S5_S9 : ∀ x ∈ \[[^\n]*\],\n      CheckpointBytes4ReaderFields.sourceE \(CheckpointBytes5Output.ofE x\) = x\)\n?', '',s)
 if m in {'Cons_FinishProof','T2R_Finish','SAP_FinishConsumer','SAP_FinishSaved','SAF_FinishPrepared'}:
  s=re.sub(r'\bcanonical\b *','',s)
 if m=='Cons_FinishProof':
  s='import SAF_AcceptedValue\n'+s
  s=s.replace('FinT_Model.finish_value finish v2 p2 _ saved2 alpha0 alpha1 r0 r1 weights alphas pair dot\n      s2 ha0 ha1 hw has hp hd',
   'SAF_AcceptedValue.value finish v2 p2 _ saved2 dot\n      s2 hd')
  s=s.replace('dotLaw fields.2.1 twelve','dotLaw fields.2.1 twelve finishCall')
 # All proof tops retain audits; generated pure definitions add no theorems.
 s='/- New-prefix accepted-only consumer; source of origin: lean/'+m+'.lean. -/\n'+s
 (ROOT/'lean'/f'{rename[m]}.lean').write_text(s)
# Dependency order, one module per compiler invocation.
order=[];seen=set()
def visit(m):
 if m in seen:return
 seen.add(m)
 s=(ROOT/'lean'/f'{rename[m]}.lean').read_text()
 for i in re.findall(r'^import (\S+)',s,re.M):
  if i in rename.values():visit(next(k for k,v in rename.items() if v==i))
 order.append(rename[m])
visit('SAF_FinalTop')
assert len(order)==len(old),(len(order),len(old))
(E/'SAF_canonical_order.json').write_text(json.dumps(order,indent=2)+'\n')
print(len(order),order[:8])
