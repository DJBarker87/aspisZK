#!/usr/bin/env python3
"""Pin own current data and previously compared owned objects; zero host work."""
from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'sdk-literal-comparison-20261025';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
transports=[];bases=[]
for folder in ['sdk-current-export-20261024','sdk-current-incremental-20261024','sdk-selected-cut-export-20261025']:
 r=json.loads((E/folder/'release.json').read_text());d=Path(r['location']);assert sha(d/'manifest.json')==r['manifest_sha256'];m=json.loads((d/'manifest.json').read_text());bases.append(dict(location=str(d),manifest_sha256=r['manifest_sha256']))
 for f in m['files']:
  if f['relative'].startswith('transport/'):
   p=d/f['relative'];assert not p.is_symlink() and sha(p)==f['sha256'];transports.append(dict(module=f['relative'][10:-6].replace('/','.'),path=str(p),bytes=f['bytes'],sha256=f['sha256']))
assert len(transports)==1432
factor=json.loads((E/'s6-sdk-source-cuts-20261024/declaration-audit-input.json').read_text());pinmap={r['path']:r['sha256'] for r in factor['inputs']};factorRows=[];inputs=[]
for row in factor['modules']:
 p=Path(row['path']);assert sha(p)==pinmap[str(p)];factorRows.append(row)
 for suffix in ['', '.server','.private']:
  f=Path(str(p)+suffix)
  if f.exists():inputs.append(dict(path=str(f),bytes=f.stat().st_size,sha256=sha(f)))
refresh=[]
entry=json.loads((E/'sdk-current-export-20261024/input-pins-v2.json').read_text())['changes'][0]
accepted=json.loads((E/'sdk-current-incremental-20261024/accepted-proof-replay-source.json').read_text())
for old,new,oldh,newh,names in [(entry['historical_path'],entry['refreshed_path'],entry['historical_sha256'],entry['refreshed_sha256'],['AspisR1.S2W_EntryPrivileges.'+n for n in ['guards','readonly','writable','accepted_privileges']]),(accepted['old_object'],'/tmp/s126-current-caller-20261021-objects/AdapterRwAccepted.olean',accepted['old_object_sha256'],'2af7274977c5602baafeb1c32d24684fc2955b8e047bd277f3b8922e486fa7eb',['AspisR1.AdapterRw.Accepted.first_call','AspisR1.AdapterRw.Accepted.first_proof_shapes'])]:
 assert sha(Path(old))==oldh and sha(Path(new))==newh
 refresh.append(dict(old=old,new=new,names=names))
 for p in [Path(old),Path(new)]:
  for suffix in ['', '.server','.private']:
   f=Path(str(p)+suffix)
   if f.exists():inputs.append(dict(path=str(f),bytes=f.stat().st_size,sha256=sha(f)))
config=dict(transports=transports,factor_rows=factorRows,proof_refresh=refresh)
(P/'input.json').write_text(json.dumps(config,indent=2)+'\n')
(P/'input-pins.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),bases=bases,inputs=inputs,transport_files=transports,scope='Owner CURRENT duplicate/factor/proof-type literal guard only. Not original ROOT/current pairing, kernel reconstruction or source/native/release proof.'),separators=(',',':'))+'\n')
root=Path('/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/src/lean/Lean')
for name in ['Expr.lean','Declaration.lean']:(P/('Lean-'+name)).write_bytes((root/name).read_bytes())
(P/'api-pins.json').write_text(json.dumps({name:dict(path=str(root/name),sha256=sha(root/name)) for name in ['Expr.lean','Declaration.lean']},indent=2)+'\n')
print(json.dumps(dict(transports=len(transports),factor_rows=len(factorRows),proof_refresh_pairs=len(refresh))))
