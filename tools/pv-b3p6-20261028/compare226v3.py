"""Exact same-input emitted/native outputs: finite validation, never a theorem."""
from pathlib import Path
import ast,json,re,hashlib
D=Path('evidence/pv-b3p6-20261028');R=D/'receipts'
native=(R/'native226-v3-01/receipt/stdout.log').read_text();lean=(R/'lean-42577/receipt/stdout.log').read_text()
labels=['TRANSFER','WITHDRAWAL','BAD_TRANSFER','BAD_WITHDRAWAL'];n={};l={}
for line in native.splitlines():
 for key in labels:
  m=re.search(r'(?<![A-Z_])'+key+r'=(.*)$',line)
  if m:n[key]=m[1]
for line in lean.splitlines():
 if line.startswith('"'):
  value=ast.literal_eval(line)
  for key in labels:
   if value.startswith(key+'='):l[key]=value[len(key)+1:]
assert set(n)==set(l)==set(labels),(set(n),set(l))
rows=[]
for key in labels:
 if key.startswith('BAD_'):
  assert n[key]==l[key]=='ERR'
  rows.append({'fixture':key,'result':'Error::Public','equal':True})
 else:
  nv=ast.literal_eval(n[key]);lv=ast.literal_eval(l[key]);assert nv==lv,key
  size,data=nv;assert size==len(data)==(1455 if key=='TRANSFER' else 1427)
  rows.append({'fixture':key,'length':size,'bytes_sha256':hashlib.sha256(bytes(data)).hexdigest(),'equal':True})
record={'evidence_class':'same-input native differential: finite validation','universal_proof':False,'projection_mutable_writes':0,'fixtures':rows,'native_log':str(R/'native226-v3-01/receipt/stdout.log'),'emission_log':str(R/'lean-42577/receipt/stdout.log'),'native_log_sha256':hashlib.sha256(native.encode()).hexdigest(),'emission_log_sha256':hashlib.sha256(lean.encode()).hexdigest()}
(D/'fidelity226v3.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record))
