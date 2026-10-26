"""Report checked transport scope; never infer feasible invocation from a source graph."""
from pathlib import Path
import json,re,subprocess,hashlib
r=Path(__file__).resolve().parents[2];d=r/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026';e=d/'lift222'
y=json.loads((d/'installed-and-remaining.json').read_text());summary=json.loads((e/'lean-summary.json').read_text())
ledger=subprocess.check_output(['git','show','research:design/PRIVACY-LEDGER-20261026.md'],text=True)
rev=subprocess.check_output(['git','rev-parse','research'],text=True).strip()
ops={int(op):vid for vid,op in re.findall(r'\| (V\d+) / `op(\d+) ',ledger)}
rows=[]
for row in y['functions']:
 z=dict(row);z['research_ledger_row']=ops.get(z['id']);z['change_this_allocation']='none; source entry not installed or removed by carrier transport';rows.append(z)
(e/'entries.json').write_text(json.dumps(dict(research_revision=rev,ledger_sha256=hashlib.sha256(ledger.encode()).hexdigest(),before=dict(selected=172,open=83,sufficient_denominator=255,native_types=26,root_premises_removed=0),after=dict(selected=172,open=83,sufficient_denominator=255,native_types=26,root_premises_removed=0),exact_invocation_denominator=None,functions=rows,type_entries=y['type_entries']),indent=2)+'\n')
lines=['# Entry and reachability table','','Unchanged:172 selected /83 open /255 sufficient source fields; exact feasible-native invocation denominator unestablished. Transport proofs do not install source operation bodies or native types. Root premises removed:0. Ledger rows refer to research revision `'+rev+'`.','','| Field | Operation | Required source bound | Selection | Ledger |','|---:|---|---|---|---|']
for z in rows:lines.append(f"|{z['id']}|`{z['name']}`|{z['required_by_source_bound']}|{z['status']}; `{z['theorem']}`|{z['research_ledger_row'] or 'already-selected/no open op row'}|")
(e/'ENTRIES.md').write_text('\n'.join(lines)+'\n')
lines=['# Native lower type table','','Before26/28; after26/28. File-world/Drop is separate from its installed descriptor value. Native Error and Formatter remain open.','','| Type | Name | Status / evidence |','|---:|---|---|']
for z in y['type_entries']:lines.append(f"|{z['id']}|`{z['name']}`|{z['status']}; `{z.get('theorem','OPEN')}`; {z.get('support','')}|")
(e/'TYPES.md').write_text('\n'.join(lines)+'\n')
latest={}
for z in summary['attempts']:
 if z['exit_status']==0:latest[z['module']]=z
bindings=[];names=[]
for mod,z in sorted(latest.items()):
 f=r/'docs/research/v8-r0-zk-20261009/lean'/(mod+'.lean');s=f.read_text();assert hashlib.sha256(s.encode()).hexdigest()==z['source_sha256'],mod
 ns=re.search(r'namespace ([\w.]+)',s)[1]
 names += [ns+'.'+n for n in re.findall(r'(?m)^theorem ([\w.]+)',s)]
 bindings.append(dict(module=mod,attempt=z['attempt'],source_sha256=z['source_sha256'],local_source=str(f.relative_to(r))))
(e/'accepted-source-binding.json').write_text(json.dumps(bindings,indent=2)+'\n')
(e/'accepted-theorems.json').write_text(json.dumps(sorted(set(names)),indent=2)+'\n')
print('accepted modules',len(bindings),'theorems',len(set(names)),'Lean',summary['compiles'],'remaining',summary['remaining'])
