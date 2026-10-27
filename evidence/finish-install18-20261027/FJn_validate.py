"""Validate retained task evidence only; does not launch compilers or builds."""
from pathlib import Path
import hashlib,json,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
subprocess.run(['python3',str(P/'FJn_receipts.py')],check=True,capture_output=True)
x=json.loads((P/'FJn_receipts.json').read_text())
rows=x['attempts'];green=[r for r in rows if r['exit_status']==0]
standard={'propext','Classical.choice','Quot.sound'}
bad=[]
for r in green:
 for line in r['print_axioms']:
  m=re.search(r'axioms: \[(.*?)\]',line,re.S)
  if m and not set(re.split(r',\s*',m.group(1).strip()))<=standard:bad.append(dict(attempt=r['attempt'],line=line))
mods=list((R/'lean').glob('FJn_*.lean'))
forbidden=[]
for f in mods:
 for i,line in enumerate(f.read_text().splitlines(),1):
  if re.search(r'\b(sorry|admit|native_decide|axiom)\b',line) and not line.lstrip().startswith(('--','/--')):forbidden.append([str(f.relative_to(R)),i,line])
  if re.search(r'set_option\s+(maxRecDepth|maxHeartbeats)',line):forbidden.append([str(f.relative_to(R)),i,line])
base=subprocess.check_output(['git','rev-parse','20860eb59a^'],text=True).strip()
changed=subprocess.check_output(['git','diff','--name-only',base],text=True).splitlines()
wrong=[f for f in changed if not (f.startswith('lean/FJn_') or f.startswith('evidence/finish-install18-20261027/'))]
out=dict(charged_attempts=x['charged_attempts'],compiler_starts=x['lean_used'],kani_used=x['kani_used'],passes=len(green),errors=len(rows)-len(green),current_modules=len(mods),unverified_current=x['unverified_current'],bad_accepted_axioms=bad,forbidden_source=forbidden,outside_owned_paths=wrong,max_rss_kib=max(int(r['peak_rss_kib']) for r in rows),all_swaps_zero=all(str(r['swaps'])=='0' for r in rows),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),method='Focused exact-source receipts on reused coherent SInt2 cache; not a fresh release rebuild')
(P/'FJn_validation.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
