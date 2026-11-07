from pathlib import Path
import re,json
E=Path(__file__).resolve().parent
s=(E/'NMX_R3_RegistryEmitted.lean').read_text();head=s[s.index('def body'):s.index('  := do')];code=s[s.index('  := do')+8:s.index('\nend NMX_R3_RegistryEmitted')].splitlines()
while code and not code[0].strip():code.pop(0)
while code and not code[-1].strip():code.pop()
ind=lambda x:len(x)-len(x.lstrip())
U8='U8';Key='Array U8 32#usize';Slice='Slice U8';P='solana_pubkey.Pubkey';Unit='Unit'
R=lambda v:'aspis_statement.pool_v1.verifier_registry.VerifierRegistry'+v
EN=lambda v:'aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntry'+v
base={'ops':'Ops','verifier_program':P,'pool_program':P,'master_account':'r1_pool_adapter.owned.OwnedAccount','master':'aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1','registry_account':'r1_pool_adapter.owned.OwnedAccount','entry_account':'r1_pool_adapter.owned.OwnedAccount','current_slot':'U64'}
ctx=dict(base);payload={};cfpayload={};matchstack=[];nodes=[];i=0
while i<len(code):
 line=code[i];txt=line.strip();n=ind(line)
 lm=re.match(r'let (\w+) ←(.*)',txt)
 if lm:
  x=lm[1];pieces=[lm[2].strip()];j=i+1
  while j<len(code) and ind(code[j])>n:pieces.append(code[j].strip());j+=1
  expr=' '.join(pieces)
  if x.startswith('cf'):
   m=re.search(r'branch (r\d*)$',expr);assert m,(x,expr);cfpayload[x]=payload[m[1]]
  elif re.fullmatch(r'r\d*',x):
   op=re.search(r'ops\.op(\d+)',expr)
   if op:payload[x]={'15':Unit,'31':R('V1'),'32':EN('V1'),'33':R('V2'),'34':EN('V2'),'38':P}[op[1]]
   elif 'require_readonly_account' in expr:payload[x]=Unit
   elif 'OwnedAccount.data' in expr:payload[x]=Slice
   elif 'map_err' in expr:
    m=re.search(r'\b(r\d*) \(\)$',expr);assert m,expr;payload[x]=payload[m[1]]
   else:raise AssertionError((x,expr))
  elif x.startswith('b'):ctx[x]='Bool'
  elif x.startswith('i'):ctx[x]=U8
  elif x.startswith(('a','p')) or x in ['loader','registry_program']:ctx[x]=Key
  elif x.startswith('s'):ctx[x]=Slice
  else:raise AssertionError((x,expr))
  i=j;continue
 mm=re.fullmatch(r'match (cf\d*) with',txt)
 if mm:
  matchstack=[m for m in matchstack if m[0]<n];matchstack.append((n,mm[1]));i+=1;continue
 if txt.startswith('|'):
  j=i;parts=[]
  while '=>' not in code[j]:parts.append(code[j].strip());j+=1
  pat,tail=code[j].strip().split('=>',1);parts.append(pat);full=' '.join(parts).strip()
  m=re.fullmatch(r'\| core\.ops\.control_flow\.ControlFlow\.(Continue|Break) (\w+|_)',full);assert m,full
  if m[1]=='Continue':
   which=next(v for k,v in reversed(matchstack) if k==n)
   if m[2]!='_':ctx[m[2]]=cfpayload[which]
   assert not tail.strip(),('inline branch unsupported',tail)
   start=j+1;end=start
   while end<len(code) and (not code[end].strip() or ind(code[end])>n):end+=1
   nodes.append({'id':len(nodes)+1,'start':start,'end':end,'ctx':dict(ctx),'case':which})
  i=j+1;continue
 i+=1
# Determine lexical free input names, excluding declarations and branch binders.
known=set(ctx)|set(base)
for nd in nodes:
 text='\n'.join(code[nd['start']:nd['end']]);declared=set(re.findall(r'\blet (\w+)\s*(?:←|:=)',text))
 declared.update(re.findall(r'ControlFlow\.(?:Continue|Break)\s+(\w+)\s*=>',text))
 used={x for x in re.findall(r'(?<![\w.])([A-Za-z_]\w*)',text) if x in nd['ctx']}
 nd['free']=[x for x in base if x in used and x not in declared]+sorted(used-declared-set(base))
 nd['types']={x:nd['ctx'][x] for x in nd['free']}
# A child continuation is replaced only at its own root, preserving all arguments.
def factor(start,end):
 chosen=[]
 for nd in nodes:
  if start<=nd['start'] and nd['end']<=end and (nd['start'],nd['end'])!=(start,end):
   if not any(p['start']<=nd['start'] and nd['end']<=p['end'] for p in chosen):chosen.append(nd)
 out=[];i=start
 for nd in sorted(chosen,key=lambda x:x['start']):
  out+=code[i:nd['start']];out.append(' '*ind(code[nd['start']])+'native'+str(nd['id']).zfill(3)+' '+' '.join(nd['free']));i=nd['end']
 out+=code[i:end]
 if not out:raise AssertionError((start,end))
 shift=min(ind(x) for x in out if x.strip())
 return '\n'.join('  '+x[shift:] if x.strip() else '' for x in out)
out='import NMX_R3_RegistryEmitted\nset_option autoImplicit false\nnoncomputable section\nnamespace NMX_R3_RegistryNativeParts\nopen Aeneas Aeneas.Std Result ControlFlow Error AdapterRw\n'
for nd in sorted(nodes,key=lambda x:x['start'],reverse=True):
 params=' '.join('('+x+' : '+nd['types'][x]+')' for x in nd['free'])
 out+='\ndef native'+str(nd['id']).zfill(3)+' '+params+' : Result (core.result.Result Unit solana_program_error.ProgramError) := do\n'+factor(nd['start'],nd['end'])+'\n'
root=head.replace('def body','def native000',1)+'  := do\n'+factor(0,len(code))
out+='\n'+root+'\n\nend NMX_R3_RegistryNativeParts\nend\n';(E/'NMX_R3_RegistryNativeParts.lean').write_text(out)
(E/'NMX_REGISTRY_PARTS.json').write_text(json.dumps({'source':'NMX_R3_RegistryEmitted.lean','parts':[{k:v for k,v in x.items() if k!='ctx'} for x in nodes],'method':'each complete Continue subtree factored once, exact free input arguments; no source expression changed'},indent=2)+'\n');print('Factored',len(nodes),'typed native continuations')
