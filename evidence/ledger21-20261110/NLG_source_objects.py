from pathlib import Path
import json,hashlib,lzma,re
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest();out=[]
loaded={json.loads(l)['module']for l in(E/'NLG_LOADED_scan.jsonl').read_text().splitlines()}
for folder,pre in [('tx2-resume2-20261109','NKU'),('row-bridges-20261109','NKY')]:
 p=E.parent/folder;receipts=[(q,json.loads(q.read_bytes()))for q in sorted(p.glob(pre+'_L*/receipt.json'))]
 for src in sorted(p.glob(pre+'_*.lean')):
  if src.stem not in loaded:continue
  b=src.read_bytes();h=H(b);hits=[]
  for q,r in receipts:
   if r['exit_status']!=0:continue
   for n,v in r['source_hashes'].items():
    if Path(n).name==src.name and v==h:
     # An actual compiler invocation, not merely an input to an audit driver.
     if r['kind']=='lean'and (str(src.stem)in str(r['command'])):hits.append(dict(receipt=str(q),source=n,source_revision=r['source_revision']))
  assert hits,(str(src),'no successful compile at current source hash')
  assert not re.search(r'^\s*(axiom\s|.*:=\s*(sorry|admit)\b)',b.decode(),re.M),src
  out.append(dict(module=src.stem,source=str(src),sha256=h,compiled=hits[-1]))
(E/'NLG_SOURCE_OBJECT_REVIEW.json').write_text(json.dumps(dict(status='PASS_COMMITTED_SOURCE_HASHES_MATCH_SUCCESSFUL_COMPILES',sources=out,objects='Retained export hashes checked during NLG seeding and final selected-object pinning; source/ELF/extraction fidelity remains P6/D188'),indent=1)+'\n');print(json.dumps(dict(source_modules=len(out),status='PASS')))
