"""Install ALL reified Result operators at the extracted proof-account entry."""
from pathlib import Path
import re,json,hashlib,sys
E=Path('evidence/pv-evh8-20261101');p=Path('lean/PV_EVH_OpSaltsProver.lean');s=p.read_text()
leaves={'applyCallees':('ApplyMaterial','ha'),'saltStep':('PrivateSaltStep','hsaltStep'),'prepare':('PrepareOpening','hprepare'),'publish':('PublishCompact','hpublish'),'materialCallees':('MaterialFromEntropy','hmaterial')}
# PrivateSalts' two operators are already installed by OpPrivateSaltsFlow.
pre,rest=s.split('def entry_OPEN',1);ds,rest=rest.split(' :=\n',1);_,rest=rest.split('\ntheorem entry_fixed',1);ts,_=rest.split(' := by\n',1)
args=ts.split('FinishedView (entry_OPEN ',1)[1].split(')\n      (RealR1_client',1)[0]
def install_args(s):
 for var,(n,_) in leaves.items():s=re.sub(r'\b'+var+r'\b','(PV_EVH_OperatorInstall.'+n+'.install '+var+' frames)',s)
 return s
for n,_ in leaves.values():
 ds=ds.replace('PV_EVH_Op'+n+'.Callees','PV_EVH_OperatorInstall.'+n+'.Leaves')
 ts=ts.replace('PV_EVH_Op'+n+'.Callees','PV_EVH_OperatorInstall.'+n+'.Leaves').replace('PV_EVH_Op'+n+'.Compatible','PV_EVH_OperatorInstall.'+n+'.Compatible')
pre=pre.replace('namespace PV_EVH_OpSaltsProver','namespace PV_EVH_OperatorProver')
out='import PV_EVH_OpSaltsProver\nimport PV_EVH_OperatorInstall\n'+pre+'def entry_OPEN'+ds+' :=\n  PV_EVH_OpSaltsProver.entry_OPEN '+install_args(args)+'\n\ntheorem entry_fixed'+ts+' := by\n  exact PV_EVH_OpSaltsProver.entry_fixed '+install_args(args)+'\n    '
hyp='he guard_fixed same account_fixed hh hb hr hf fallible_same path_same nonce_same ha hbuild hsaltLeaves hsaltStep hprepare hfinish hpublish hmaterial frame_fixed selected'
for var,(n,h) in leaves.items():hyp=re.sub(r'\b'+h+r'\b','(PV_EVH_OperatorInstall.'+n+'.install_fixed '+var+' '+h+' frames frame_fixed selected)',hyp)
out+=hyp+'\n\n#print axioms entry_fixed\nend PV_EVH_OperatorProver\n'
q=Path('lean/PV_EVH_OperatorProver.lean');r=E/'operator-prover-generation.json';record=json.dumps(dict(source=str(p),source_sha256=hashlib.sha256(s.encode()).hexdigest(),output_sha256=hashlib.sha256(out.encode()).hexdigest(),status='source operator installation; native callbacks/drop/runtime still OPEN',rows_removed=[]),indent=2)+'\n'
if '--check' in sys.argv:assert q.read_text()==out and r.read_text()==record
else:q.write_text(out);r.write_text(record)
print('Generated installed operator entry; native callback/drop/runtime laws remain OPEN')
