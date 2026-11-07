"""Restate only the rev3-affected registry VALUE transport cone under NNH_.
No existing proved module or supplier is edited. Native bodies are unchanged.
"""
from pathlib import Path
import re,json,hashlib,subprocess,sys
E=Path(__file__).resolve().parent;D=Path('evidence/model-bridge-20261111')
seen=set();order=[];deps={}
def visit(m):
 if m in seen:return
 seen.add(m);p=D/(m+'.lean')
 if not p.exists():return
 deps[m]=re.findall(r'^import (NND_\w+)',p.read_text(),re.M)
 for c in deps[m]:visit(c)
 order.append(m)
visit('NND_RegistryReturned');affected=set()
for m in order:
 if m in ['NND_AccountCarrier','NND_RegistryEval']or any(c in affected for c in deps[m]):affected.add(m)
rename={m:'NNH_M'+m[4:] for m in affected};rename['NND_RegistryEval']='NNH_RegistryEval'
# Three old carrier modules extend one namespace. Keep pure, unaffected
# converters in NND_Carrier and put every new carrier declaration in own namespace.
newcarrier=['account','accounts','outer','getter','accounts_length','account_fields','fromBytes','from_bytes','bytes_from','bytes_bound','length','readonly','readonly_buffer']
rows=[];plan=[]
for m in order:
 if m not in affected or m=='NND_RegistryEval':continue
 src=D/(m+'.lean');raw=src.read_text();s=raw
 for old,new in sorted(rename.items(),key=lambda z:-len(z[0])):s=re.sub(r'\b'+re.escape(old)+r'\b',new,s)
 s=s.replace('namespace NND_Carrier','namespace NNH_ModelCarrier').replace('end NND_Carrier','end NNH_ModelCarrier')
 for n in newcarrier:s=re.sub(r'\bNND_Carrier\.'+n+r'\b','NNH_ModelCarrier.'+n,s)
 # Own namespace retains access to immutable pure carrier converters.
 if 'namespace NNH_ModelCarrier' in s:s=s.replace('namespace NNH_ModelCarrier','namespace NNH_ModelCarrier\nopen NND_Carrier')
 # Both namespaces are available to unqualified carrier expressions.
 if m!='NND_AccountCarrier':
  s=s.replace('open NND_Carrier','open NND_Carrier NNH_ModelCarrier')
  s=re.sub(r'(open [^\n]*\bNND_Carrier)(\n)',r'\1 NNH_ModelCarrier\2',s)
  # Some files use a single unqualified outer/bytes without the original namespace.
  # Their direct imported carrier modules already establish these names via open.
 s=re.sub(r'(\(account \w+\))\.data_len\b',r'\1.length',s)
 s=re.sub(r'(\(account \w+\))\.data\b',r'\1.bytes',s)
 s=s.replace('a.registry_account.data','a.registry_account.bytes').replace('a.entry_account.data','a.entry_account.bytes')
 s=s.replace('RSL.OwnedAccount.data_len,','').replace('RSL.OwnedAccount.data_len','').replace('RSL.OwnedAccount.data,','').replace('RSL.OwnedAccount.data','')
 if m!='NND_AccountCarrier':s=''.join(line.rstrip('\n')+' NNH_ModelCarrier\n' if line.startswith('open ')and'NND_Carrier' in line and'NNH_ModelCarrier'not in line else line for line in s.splitlines(keepends=True))
 # Parent evaluator already has the rev3 clone-allocation-aware restatement.
 # Every new theorem is printed by the inherited declarations (checked below).
 for n in re.findall(r'^(?:@\[[^\n]*\]\s*)?(?:theorem|lemma)\s+(\w+)',s,re.M):
  assert '#print axioms '+n in s,(m,n)
 out=E/(rename[m]+'.lean')
 if '--check' in sys.argv:assert out.read_text()==s,str(out)
 else:out.write_text(s)
 rows.append(dict(source=str(src),source_sha256=hashlib.sha256(raw.encode()).hexdigest(),destination=str(out),destination_sha256=hashlib.sha256(s.encode()).hexdigest(),changes='prefix/namespace; raw RSL bytes/length getter values at rev3; original native methods preserved'))
 plan.append(rename[m])
if '--check' not in sys.argv:(E/'NNH_REGISTRY_PORT.json').write_text(json.dumps(dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),modules=rows,compile_order=plan,retained_modules=[m for m in order if m not in affected],reused_evaluator='NNH_RegistryEval (rev3 rebuilt)'),indent=2)+'\n')
print('new modules',len(plan))
