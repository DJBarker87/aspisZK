from pathlib import Path
import hashlib,json,re
E=Path(__file__).resolve().parent;R=E.parent.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def ref(p):return dict(path=str(p.relative_to(R)),sha256=sha(p.read_bytes()))
def theorem(module,name,folder=E):
 source=folder/(module+'.lean');text=source.read_text();full=module+'.'+name
 receipts=sorted(folder.glob('*/receipt.json'))
 for p in receipts:
  r=json.loads(p.read_text())
  if r.get('kind')=='lean' and r.get('exit_status')==0 and any(l.startswith("'"+full+"'") for l in r.get('print_axioms',[])):
   key=next((k for k,v in r['source_hashes'].items() if v==sha(source.read_bytes()) and k.endswith(module+'.lean')),None)
   if key:break
 else:raise ValueError('no successful exact source audit for '+full)
 m=re.search(r'(?m)^\s*theorem '+re.escape(name)+r'\b',text);assert m
 start=m.start();next_decl=re.search(r'(?m)^(?:\s*theorem |\s*def |#print |end )',text[m.end():])
 end=m.end()+next_decl.start() if next_decl else len(text)
 statement=text[start:end].strip()+'\n'
 return dict(name=full,source=ref(source),receipt=ref(p),snapshot_path=key,statement=statement,statement_sha256=sha(statement.encode()))
def native_support(attempts):
 return [ref(E/n) for a in attempts for n in [a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-metadata-pin.json',a+'-source-check.json',a+'-rule16-check.json',a+'-NEQ_native_contracts.patch',a+'-NEQ_oracle.patch']]
