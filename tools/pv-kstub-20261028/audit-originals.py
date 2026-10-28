from pathlib import Path
import json,subprocess,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-kstub-20261028';P=R/'evidence/pv-relink-20261028'
sha=lambda b:hashlib.sha256(b).hexdigest()
def body(s,name):
 m=re.search(r'fn '+name+r'(?:<[^\n]*>)?\(',s);assert m,name
 a=s.index('{',m.start());d=1;i=a+1
 while d:d+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[m.start():i]
rows=[]
for p in json.loads((E/'plans.json').read_text()):
 idx=p['index'];receipt=P/p['row']/f'suspended-{idx}-receipt.txt';rev=json.loads(receipt.read_text())['source_revision']
 if p['package']=='cb':path='tools/pv-cb-20261026/proof/lib.rs'
 elif p['package']=='cblib':path='tools/pv-cblib-20261027/kani-lib.rs'
 elif idx==151:path='tools/pv-cb3-20261026/arbitrary_bytes.rs'
 elif idx==152:path='tools/pv-cb3-20261026/kani-lib.rs'
 else:
  # Original frozen block-buffer proof append is retained by the row source receipt.
  rows.append(dict(index=idx,window=p['window'],authority=str(receipt.relative_to(R)),reference='tools/pv-alib-20261027/split-flat-reference.rs',comparison='original body retained except harness rename and additional n<=64 / n>64 assumption; inspect split source snapshots'));continue
 b=subprocess.check_output(['git','show',rev+':'+path],cwd=R)
 try:s=body(b.decode(),p['harness'])
 except AssertionError:
  # Receipts can precede their harness commit; resolve against the retained historical source hash first.
  inp=json.loads(receipt.read_text()).get('inputs',{})
  expected=[v['sha256'] for k,v in inp.items() if k.endswith('/lib.rs') and '/kani-proof/' in k]
  resolved=None
  for candidate in subprocess.check_output(['git','log','--all','--format=%H','--',path],cwd=R,text=True).splitlines():
   data=subprocess.check_output(['git','show',candidate+':'+path],cwd=R)
   if expected and sha(data) in expected:resolved=(candidate,data);break
  if resolved:rev,b=resolved;s=body(b.decode(),p['harness'])
  else:
   # Full current source exists in frozen Kscan package; later append-only history may bind a prefix.
   for candidate in subprocess.check_output(['git','log','--all','--format=%H','--',path],cwd=R,text=True).splitlines():
    data=subprocess.check_output(['git','show',candidate+':'+path],cwd=R)
    try:test=body(data.decode(),p['harness'])
    except AssertionError:continue
    if sha(test.encode())==p['body_sha256']:rev,b,s=candidate,data,test;break
   else:raise RuntimeError(p['harness'])
 if idx==152:s=s.replace('super::reference_p6::wide_bytes_flat','wide_bytes_flat')
 if sha(s.encode())!=p['body_sha256']:print('MISMATCH',p['harness']);(E/(p['harness']+'-original.rs.txt')).write_text(s)
 blob=subprocess.check_output(['git','rev-parse',rev+':'+path],cwd=R,text=True).strip();rows.append(dict(index=idx,harness=p['harness'],revision=rev,path=path,blob=blob,source_sha256=sha(b),body_sha256=sha(s.encode()),original_body_equal=sha(s.encode())==p['body_sha256']))
(E/'original-body-bindings.json').write_text(json.dumps(rows,indent=2)+'\n');print(len(rows),'original body bindings checked')
