from pathlib import Path
import subprocess,json,re,hashlib
P=Path(__file__).resolve().parent; pins=json.loads((P/'pins.json').read_text()); R='docs/research/v8-r0-zk-20261009/lean/R1Z/'
def src(k,m):return subprocess.check_output(['git','show',pins[k]+':'+R+m+'.lean']).decode()
def symbols(k,m):
 s=src(k,m); stack=[];out=[]
 for line in s.splitlines():
  n=re.match(r'namespace\s+(\S+)',line)
  if n:stack.append(n[1])
  n=re.match(r'end(?:\s+(\S+))?\s*$',line)
  if n and stack and (n[1] is None or n[1]==stack[-1]):stack.pop()
  n=re.match(r'(?:protected\s+)?(?:theorem|structure)\s+(\w+)',line)
  if n:out.append(('.'.join(stack+[n[1]]),line.startswith('structure')))
 return out
report=subprocess.check_output(['git','show',pins['cb']+':evidence/pv-cb-20261026/RESUME-SOURCE-ROWS.md']).decode()
cb=[]
for line in report.splitlines():
 if 'ROW-DISCHARGED(candidate)' in line:
  theorem=line.split('|')[4];m=theorem.split('.')[1];cb.append(('cb',m,[(theorem,False)]))
plans=[]
for i in range(0,len(cb),4):plans.append(('Callbacks'+str(i//4+1),cb[i:i+4]))
others=[('Cb3',[('cb3',x) for x in ['PV_CB3_Op120Source','PV_CB3_Op225Source','PV_CB3_Op246Source','PV_CB3_Op51Arbitrary']]),('Dictionary',[('dict','PDict_PureDictionary'),('dict','PDict_CodecDictionary'),('dict','PDict_RemainingDictionary231')]),('Formatter',[('dict','PDict_OwnedCorrect262')]),('RwCompression',[('rw','ProverRw19P6Join'),('rw','ProverRw19P6ContextIdentity')]),('RwModel',[('rw','ProverRw19AssemblyCallerIff')]),('RwSource',[('rw','PV_TraceValueInstall'),('rw','PV_ProverRwP7CoefficientsInstall')]),('SourceIdentification',[('srcid','PV_Src_NativeIdentification')]),('SourceConsumer',[('srcid','PV_Src_Identification')]),('RunJoinEndpoint',[('runjoin','PV_RunJoin_Endpoint')]),('RunJoinTrust',[('runjoin','PV_RunJoin_TrustItems'),('runjoin','PV_RunJoin_TrustEndpoint')]),('RunJoinCandidate',[('runjoin','PV_RunJoin_TrustLedger')]),('JoinConsumer',[('join','ProverRwP6BodyData')]),('JoinCanonical',[('join','PV_Join_CurrentPolynomialCanonical5')]),('Headline',[('research','PrivacyR1HeadlineDeployedReal')])]
for label,ms in others:plans.append((label,[(k,m,symbols(k,m)) for k,m in ms]))
assert len(plans)==20,len(plans)
checks=[]
for label,ms in plans:
 name='PV_Ledger_Recount3_'+label;s='\n'.join('import R1Z.'+m for k,m,ss in ms)+'\nset_option pp.explicit true\n'
 items=[]
 for k,m,ss in ms:
  for n,struct in ss:
   s+=('#print '+n+'\n') if struct else ('#check @'+n+'\n#print axioms '+n+'\n')
   items.append([m,n])
 file=P/'helpers'/(name+'.lean');file.parent.mkdir(exist_ok=True);file.write_text(s)
 checks.append(dict(module=name,source=str(file.relative_to(P)),sha256=hashlib.sha256(s.encode()).hexdigest(),items=items,imports=[dict(ref=k,module=m,source_sha256=hashlib.sha256(src(k,m).encode()).hexdigest()) for k,m,ss in ms]))
(P/'checks.json').write_text(json.dumps(checks,indent=2)+'\n');print(len(checks),[(c['module'],len(c['items'])) for c in checks])
