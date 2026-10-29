"""Prepare owned candidates, preserving program bodies; no row credit here."""
from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-rdcd3-20261028'
plan=json.load(open(E/'v217-thin-plan.json'))
mp={n:('PV_RDCD3_CB_'+n[6:] if n.startswith('PV_CB_') else 'PV_RDCD3_'+n) for n in plan['order']}
mp.update(ProverRwP7CurrentFieldSource='PV_RDCD3_FieldSource',PV_CB_CurrentTotal='PV_RDCD3_FieldTotal',ProverRwSuccessReverseRange='PV_RDCD3_ReverseRange',ProverRwP6ArrayRead='PV_RDCD3_ArrayRead',ProverRwSuccessPowerTotal='PV_RDCD3_LoopUnfold',ProverRwSuccessPointsTotal='PV_RDCD3_ArrayTotal',ProverCommitArrayIndex25='PV_RDCD3_ArrayIndex',ProverRwSuccessArithmeticTotal='PV_RDCD3_Total',ProverRwDictionaryTower='PV_RDCD3_Total')
def rename(s):
 for a,b in sorted(mp.items(),key=lambda x:-len(x[0])):s=s.replace(a,b)
 return re.sub(r'^set_option max(?:Heartbeats|RecDepth).*\n','',s,flags=re.M)
records=[]
for n in plan['order']:
 if n in ['ProverRwP7CurrentFieldSource','PV_CB_CurrentTotal']:continue
 original=(L/(n+'.lean')).read_text()
 if n in ['ProverRwSuccessReverseRange','ProverRwP6ArrayRead']:
  original=re.sub(r'^import .*\n','import Aeneas\n',original,count=1)
 elif n=='ProverRwSuccessPowerTotal':
  body=original[original.index('theorem loop_bind'):original.index('theorem pow_unfold')]
  original='import Aeneas\nnamespace R1Z.ProverRwSuccessPowerTotal\nopen Aeneas Aeneas.Std Result ControlFlow\n'+body+'\n#print axioms loop_bind\nend R1Z.ProverRwSuccessPowerTotal\n'
 elif n=='ProverRwSuccessPointsTotal':
  body=original[original.index('theorem update_total'):original.index('theorem finite_total')]
  original='import R1Z.PV_RDCD3_Total\nnamespace R1Z.ProverRwSuccessPointsTotal\nopen Aeneas Aeneas.Std Result PV_RDCD3_Total\n'+body+'\n#print axioms update_total\nend R1Z.ProverRwSuccessPointsTotal\n'
 out=rename(original)
 if n=='PV_CB_MaskLeaves':
  out=out.replace('apply bind_total ((congrArg PV_RDCD3_Total.Total (PV_CB_CurrentNeg.native x.b)).mpr (m_neg _))','apply bind_total (PV_RDCD3_FieldTotal.m_neg x.b)')
 p=L/(mp[n]+'.lean');p.write_text(out)
 records.append(dict(original=n,owned=mp[n],original_sha256=hashlib.sha256((L/(n+'.lean')).read_bytes()).hexdigest(),owned_sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
(E/'v217-owned-candidates.json').write_text(json.dumps(dict(mapping=mp,records=records,changes='Namespace/import transport only for program definitions; extracted standalone generic helper lemmas at dependency cuts; resource overrides removed; MaskLeaves neg totality will use directly proved current body. No existing module edited.',status='DRAFT, no row credit; all changed generic helpers and full source gate required'),indent=2)+'\n')
print('Prepared',len(records),'owned candidate modules; no row credit')
