from pathlib import Path
import json,lzma,subprocess,hashlib
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest();J=lambda p:json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
b=J(E.parent/'ledger19-20261108/NKN_LEDGER.json.xz');by={r['row']:r for r in b['rows']};rows=[];pins={}
for folder,pre in [('circle-points','NKM'),('terminal4','NKI'),('batch-merkle3','NKL'),('tx2-adapters2','NKP')]:
 for f in J(E.parent/(folder+'-20261108')/(pre+'_CLOSED.json'))['functions']:
  for rid in f.get('rows',[f.get('row')]):
   r=by[rid];file,name=r['function'].split('::',1);text=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+file]);pins[file]=H(text);t=text.decode();p=t.index('fn '+name+'(');p=t.index('{',p);q=p+1;d=1
   while d:d+=(t[q]=='{')-(t[q]=='}');q+=1
   inner=H(t[p+1:q-1].encode());braces=H(t[p:q].encode());assert r['frozen_body_sha256']==braces,(rid,braces)
   submitted=f.get('frozen_body_sha256');assert submitted in [inner,braces],rid
   rows.append(dict(row=rid,file=file,source_sha256=H(text),basis_braced_body=braces,candidate_body=submitted,candidate_hash_shape='without outer braces'if submitted==inner else'with outer braces',same_frozen_function=True))
# Read-only frozen identity: no shipped edits in this job.
diff=subprocess.run(['git','diff','--name-only','HEAD','--','crates','programs','Cargo.lock'],capture_output=True,text=True);assert not diff.stdout
(E/'NKW_SOURCE_REVIEW.json').write_text(json.dumps(dict(status='PASS',rows=rows,frozen_file_pins=pins,shipped_worktree_diff=[],NKI_hash_difference='Exactly two outer braces; both recomputed from SAME frozen source. No function substitution or source drift.'),indent=1)+'\n');print('All10 frozen bodies matched; NKI hashes differ solely by outer braces')
