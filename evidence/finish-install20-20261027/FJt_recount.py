"""Read-only exact signature comparison and Rc12 atomic-family recount."""
from pathlib import Path
import copy,hashlib,json,re,sys
E=Path(__file__).resolve().parent; R=E.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def norm(s):return re.sub(r'\s+',' ',s).strip()
def save(n,x):(E/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
for f,h in json.loads((E/'FJt_BASELINE.json').read_text()).items():assert sha(R/f)==h,f
attempt=sys.argv[1] if len(sys.argv)>1 else 'FJt_060'
receipt=json.loads((E/attempt/'receipt.json').read_text());assert receipt['exit_status']==0
log=(E/attempt/'stdout.log').read_text();assert 'error:' not in log and 'sorryAx' not in log
names=['AspisR1.ARX_Root.deployed','AspisR1.IDa_Deployed.ARX_Deployed','AspisR1.FJt_Deployed.deployed']
starts=[log.index('@'+n+' :') for n in names]
end=log.index('def AspisR1.FIp_GlobalOwners.Owners',starts[-1])
parts=[log[starts[0]:starts[1]],log[starts[1]:starts[2]],log[starts[2]:end]]
for n,p in zip(['FJt_ARX_Root.BEFORE.lean.txt','FJt_ARX_Deployed.BEFORE.lean.txt','FJt_Deployed.AFTER.lean.txt'],parts):
 assert not any(t in p for t in ['⋯','...','sorryAx'])
 (E/n).write_text(p)
expected=norm(parts[0]).replace('@'+names[0],'@'+names[1],1)
oldbinder='(c : AspisR1.DrvC_Installation.Configuration AspisR1.FIo_Install.W CoreError)'
newbinder='(missing : AspisR1.IDa_Deployed.Uninstalled CoreError)'
assert expected.count(oldbinder)==1
expected=expected.replace(oldbinder,newbinder)
expected=re.sub(r'\bc\b','(@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing indexError reservation)',expected)
assert expected==norm(parts[1]),'IDa substitution changed'
expected=norm(parts[1]).replace('@'+names[1],'@'+names[2],1)
assert expected.count('AspisR1.FIp_GlobalOwners.Owners')==1
assert expected.count('AspisR1.FIs_Result.Outcome')==1
expected=expected.replace('AspisR1.FIp_GlobalOwners.Owners','AspisR1.FJt_GlobalOwners.Owners').replace('AspisR1.FIs_Result.Outcome','AspisR1.FJt_Result.Outcome')
assert expected==norm(parts[2]),'unexpected final root binder/conclusion change'
save('FJt_STATEMENT-CHECK.json',dict(attempt=attempt,full_kernel_types_without_elisions=True,configuration_substitution=dict(oldbinder=oldbinder,newbinder=newbinder,substitution='c := IDa_Deployed.deployedConfiguration missing indexError reservation',law_removals=0),specialised_root_changes=['finishOwners: FIp_GlobalOwners.Owners -> FJt_GlobalOwners.Owners','native outcome: FIs_Result.Outcome -> FJt_Result.Outcome'],other_binders_byte_identical_after_whitespace_normalisation=True,other_conclusion_changes=[],native_definition_check='FJt_NATIVE-DEFINITION-CHECK.json',all_statement_sha256={n:sha(E/n) for n in ['FJt_ARX_Root.BEFORE.lean.txt','FJt_ARX_Deployed.BEFORE.lean.txt','FJt_Deployed.AFTER.lean.txt']}))
pairs=[('FIs_Result','FJt_Result'),('FIs_Caller','FJt_BoundCaller'),('FIs_Cont','FJt_Cont'),('FIs_Literal','FJt_Literal'),('FIs_Finish','FJt_NativeFinish')]
checks={}
def outcome(module):
 s=(R/'lean'/(module+'.lean')).read_text();a=s.index('def Outcome');e=s.find('\ntheorem ',a)
 if e<0:e=s.index('\nend AspisR1.',a)
 return re.sub(r'/\-.*?\-/','',s[a:e],flags=re.S)
for oldname,newname in pairs:
 x,y=outcome(oldname),outcome(newname)
 for orig,new in pairs:y=y.replace(new+'.Outcome',orig+'.Outcome')
 if oldname=='FIs_Finish':
  x=x.replace('R3SemanticRemainingJoins.EquationEndpoint i.decoded','FJt_Remaining.Prefix').replace(' q tr) i.data)',' q tr))')
 assert norm(x)==norm(y),oldname
 checks[oldname+' -> '+newname]=dict(identical_after_named_reference_substitution=True,only_atomic_change=('EquationEndpoint public rs data -> Prefix rs (terminal removed, initial/chain retained)' if oldname=='FIs_Finish' else 'none; successor definition reference only'))
save('FJt_NATIVE-DEFINITION-CHECK.json',checks)
# Global quantifiers, source witnesses, calls and shape guards are literal copies.
def definition(module,name):
 s=(R/'lean'/(module+'.lean')).read_text();a=s.index('def '+name);e=s.find('\ntheorem ',a)
 if e<0:e=s.index('\nend AspisR1.',a)
 return s[a:e]
x=definition('FIp_GlobalOwners','Owners');y=definition('FJt_GlobalOwners','Owners').replace('FJt_Remaining.Holds','FIp_Remaining.Holds')
assert norm(x)==norm(y)
save('FJt_GLOBAL-DEFINITION-CHECK.json',dict(owner_quantifiers_witnesses_calls_shape_guards_identical=True,retained_families=['F3Y_G_L142','F3Y_G_L143','F3Y_G_L144','F3Y_G_L145'],removed=['F3Y_G_L146'],replacement='FIp_Remaining.Holds -> FJt_Remaining.Holds; Pair/matching unchanged; EquationEndpoint initial/chain retained as Prefix'))
old=json.loads((R/'evidence/recount12-20261027/Rc12_LEDGER_DELTA.json').read_text())['roots']['ARX_Root']
rows=copy.deepcopy(old['rows']);removed=['L146','F3Y_G_L146']
for k in removed:assert sum(r['id']==k and r['classification']=='P' and r['scope']=='actual antecedent' for r in rows)==1
remaining=[r for r in rows if r['id'] not in removed]
for r in remaining:r['FJt_disposition']='Retained with original scope, guards, witnesses and classification.'
def count(rs):return {c:sum(r['classification']==c for r in rs) for c in 'TPGC'}
def totals(rs):return {s:count([r for r in rs if r['scope']==s]) for s in ['actual antecedent','deployment only','deployment alias']} | {'deployment-inclusive non-alias':count([r for r in rs if r['scope']!='deployment alias']),'raw including alias':count(rs)}
assert totals(rows)==old['after']
for k in [f'L{i}' for i in range(142,146)]+[f'F3Y_G_L{i}' for i in range(142,146)]:assert any(r['id']==k for r in remaining)
save('FJt_RECOUNT.json',dict(method='Rc12/Rc11 atomic law-family ledger; split conjunction leaves, preserve SAME witnesses and parsing guards; no Fin22 multiplication; native/global separately counted; returned data/facts not premises; no alias discount.',before_theorem=names[0],configuration_only_theorem=names[1],after_theorem=names[2],adopted_before=True,adopted_after=False,baseline='evidence/recount12-20261027/Rc12_LEDGER_DELTA.json#roots.ARX_Root',before=totals(rows),after=totals(remaining),delta=dict(T=0,P=-2,G=0,C=0),removed=[r for r in rows if r['id'] in removed],added=[],reclassified=[],rows=remaining,configuration_substitution_delta=dict(T=0,P=0,G=0,C=0),adopted_ARX_unchanged_delta=dict(T=0,P=0,G=0,C=0),authoritative_ledger_edited=False,contract_edited=False))
print(json.dumps(dict(kernel_statement_check=True,before=totals(rows),after=totals(remaining),delta='0T/-2P/0G/0C'),indent=2))
