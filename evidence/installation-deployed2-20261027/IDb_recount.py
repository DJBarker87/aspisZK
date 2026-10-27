"""Read-only ledger recount and exact complete kernel type substitution."""
from pathlib import Path
from collections import Counter
import hashlib,json,re,copy
E=Path(__file__).resolve().parent; R=E.parents[1]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def norm(s): return re.sub(r'\s+',' ',s).strip()
def save(n,x): (E/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
baseline=json.loads((E/'IDb_BASELINE.json').read_text())
for p,h in baseline['files'].items(): assert sha(R/p)==h,p
log=(E/'IDb_007/stdout.log').read_text()
assert json.loads((E/'IDb_007/receipt.json').read_text())['exit_status']==0
assert 'error:' not in log
start=log.index('@AspisR1.FJu_Top.deployed :')
mid=log.index('@AspisR1.IDb_Deployed.FJu_Deployed :',start)
end=log.index('def AspisR1.IDb_Deployed.deployedConfigurationFull',mid)
before,after=log[start:mid],log[mid:end]
assert all(x not in before+after for x in ['⋯','...','sorryAx'])
(E/'IDb_FJu_Top.BEFORE.lean.txt').write_text(before)
(E/'IDb_FJu_Deployed.AFTER.lean.txt').write_text(after)
expected=norm(before).replace('@AspisR1.FJu_Top.deployed','@AspisR1.IDb_Deployed.FJu_Deployed',1)
old='(c : AspisR1.DrvC_Installation.Configuration AspisR1.FIo_Install.W CoreError)'
new='(adapter : AdapterRw.Ops) (currentBase : AspisR1CurrentCaller.Ops) (stageBase : VTop_Stages.Ops) (reserved : Bool)'
assert expected.count(old)==1
expected=expected.replace(old,new)
expr='(@AspisR1.IDb_Deployed.deployedConfigurationFull CoreError adapter currentBase stageBase reserved indexError reservation)'
expected=re.sub(r'\bc\b',expr,expected)
assert expected==norm(after), 'Complete kernel type differs beyond declared substitution'
save('IDb_STATEMENT-CHECK.json',dict(before_sha256=sha(E/'IDb_FJu_Top.BEFORE.lean.txt'),after_sha256=sha(E/'IDb_FJu_Deployed.AFTER.lean.txt'),complete_kernel_types_no_elisions=True,exact_printed_type_substitution=True,oldbinder=old,newbinder=new,substitution='c := '+expr,other_type_changes=[],proof='FJu_Top.deployed applied once in IDb_Deployed.FJu_Deployed; IDb_005 and full audit IDb_007'))
ledger=R/'evidence/finish-chain1-20261027/FJu_recount.json'
oldledger=json.loads(ledger.read_text()); rows=copy.deepcopy(oldledger['rows'])
active=[r for r in rows if r['status']!='removed']
def counts(rs):
 out={}
 for scope in ['actual antecedent','deployment only','deployment alias']:
  c=Counter(r['classification'] for r in rs if r['scope']==scope)
  out[scope]={k:c[k] for k in 'TPGC'}
 out['deployment-inclusive non-alias']={k:out['actual antecedent'][k]+out['deployment only'][k] for k in 'TPGC'}
 return out
assert counts(active)==oldledger['after_counts']
assert counts(active)['actual antecedent']==dict(T=83,P=5,G=13,C=0)
assert counts(active)['deployment-inclusive non-alias']==dict(T=89,P=22,G=13,C=0)
for r in rows:
 r['IDb_disposition']='Previously removed; no new credit' if r['status']=='removed' else 'Retained under exact implementation substitution; no new law discharged'
assert {r['id'] for r in active if r['classification']=='P' and r['scope']=='actual antecedent'}=={'L142','F3Y_G_L142','L146','F3Y_G_L146','L154'}
save('IDb_RECOUNT.json',dict(method=oldledger['method'],before_theorem='AspisR1.FJu_Top.deployed',after_theorem='AspisR1.IDb_Deployed.FJu_Deployed',ledger_source=str(ledger.relative_to(R)),ledger_sha256=sha(ledger),before=counts(active),after=counts(active),delta=dict(T=0,P=0,G=0,C=0),removed=[],added=[],reclassified=[],rows=rows,implementation_data_inputs_resolved=['query','geometry'],implementation_data_inputs_retained=['adapter','currentBase','stageBase','reserved'],inherited_data_parameters=['indexError','reservation'],adoption=False,qualification=oldledger['qualification']))
print(json.dumps(dict(kernel_substitution=True,before=counts(active),after=counts(active),delta='0T/0P/0G/0C'),indent=2))
