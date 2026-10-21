#!/usr/bin/env python3
"""Check unchanged callee contracts against their accepted source snapshot."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent
E=R/'docs/research/100bit-spend-path-20261013/evidence/s7-kani2-20261021'
sha=lambda x:hashlib.sha256(x).hexdigest()
rev='4c486e546';steps='tools/s7-kani2-20261021/src/steps.rs';lib='tools/s7-kani2-20261021/src/lib.rs'
old=subprocess.check_output(['git','show',rev+':'+steps],cwd=R).decode()
oldlib=subprocess.check_output(['git','show',rev+':'+lib],cwd=R).decode()
def declaration(s,name):
 a=s.index('fn '+name+'(');a=s.rfind('\n',0,a)+1
 while a>0:
  before=s.rfind('\n',0,a-1)+1
  if s[before:a].startswith('#['):a=before
  else:break
 b=s.index('{',a)+1;depth=1;i=b
 while depth:
  depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a:i]
records=[]
for name,attempt in [(f'lane{j}','step-04') for j in range(4)]+[('row_step','row-01')]:
 receipt=json.loads((E/'receipts'/attempt/'receipt.json').read_text())
 assert receipt['exit_status']==0
 assert receipt['source_sha256'][steps]==sha(old.encode())
 original=declaration(old,name);current=declaration((R/steps).read_text(),name)
 assert original==current,name
 records.append(dict(callee=name,accepted_attempt=attempt,source_revision_with_exact_snapshot=rev,source_file_sha256=sha(old.encode()),current_contract_declaration_sha256=sha(current.encode()),declaration_unchanged=True))
for name in ['scalar_spec','row_spec','row_safe','row_equal','k_ok']:
 assert declaration(oldlib,name)==declaration((R/lib).read_text(),name),name
records.append(dict(unchanged_helpers=['scalar_spec','row_spec','row_safe','row_equal','k_ok'],snapshot=rev+':'+lib))
mutable=E/'receipts/mutable-row-03/receipt.json'
if mutable.exists():
 r=json.loads(mutable.read_text());assert r['exit_status']==0
 current=(R/steps).read_text()
 snapshot='\n'.join(line for line in current.split('\n') if 'fn accumulator_mutable_slot_' not in line)
 assert sha(snapshot.encode())==r['source_sha256'][steps]
 assert declaration(snapshot,'update_residue_row')==declaration(current,'update_residue_row')
 (E/'verified-mutable-row-03.steps.rs.txt').write_text(snapshot)
 records.append(dict(callee='update_residue_row',accepted_attempt='mutable-row-03',accepted_snapshot_sha256=sha(snapshot.encode()),current_contract_declaration_sha256=sha(declaration(current,'update_residue_row').encode()),declaration_unchanged=True,write_footprint='modifies(row)'))
(E/'verified-callee-chain.json').write_text(json.dumps(dict(scope='Exact contract declarations and helper definitions are unchanged from accepted step-04/row-01 source, despite later unrelated roots/tooling additions. The accepted mutable-row snapshot is reconstructed by removing later unrelated fixed-slot root declarations.',checks=records),indent=2)+'\n')
print('Accepted scalar/row callee declarations and semantics helpers unchanged')
