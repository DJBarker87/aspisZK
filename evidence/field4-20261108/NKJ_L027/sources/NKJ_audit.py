from pathlib import Path
import subprocess,json,sys,re,lzma,hashlib
B=Path(__file__).resolve().parent;mode=sys.argv[1];D=B/'NKJ_audit';D.mkdir(exist_ok=True)
r=subprocess.run([str(B/'NKJ_native/NKJ_Driver'),mode],cwd=B,text=True,capture_output=True)
(D/(mode+'.log')).write_text(r.stdout+r.stderr)
results=[json.loads(z) for z in re.findall(r'NEP_RESULT (.*)',r.stdout)]
errors=[]
if mode=='fixtures':
 expected={'NEP_Planted.matcher':['NEP_Planted.matchAx'],'NEP_Planted.viaPrivate':['NEP_Planted.privateAx'],'NEP_Planted.proof':['NEP_Planted.proofAx'],'NEP_Planted.viaAux':['NEP_Planted.auxAx'],'NEP_MutateMatch.matcher':[],'NEP_MutatePrivate.viaPrivate':[],'NEP_MutateProof.proof':[],'NEP_MutateAux.viaAux':[]}
 for root,want in expected.items():
  rows=[x for x in results if x['root']==root]
  if len(rows)!=1 or rows[0]['walked_axioms']!=want or rows[0]['collect_axioms']!=want or not rows[0]['equal']:errors.append(root)
elif mode=='proof':
 roots=json.loads((B/'NKJ_AUDIT_ROOTS.json').read_text())
 if sorted(x['root'] for x in results)!=sorted(roots):errors.append('root completeness')
 for x in results:
  if not x['equal'] or set(x['walked_axioms'])-{'propext','Classical.choice','Quot.sound'}:errors.append(x['root'])
 for p in B.glob('NEP_proof_*_REACHABLE.txt'):
  raw=p.read_bytes();q=D/(p.name+'.xz');q.write_bytes(lzma.compress(raw,preset=6));(D/(p.name+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n')
  assert lzma.decompress(q.read_bytes())==raw;p.unlink()
elif mode=='scan':
 rows=[json.loads(z) for z in (B/'NKJ_LOADED_scan.jsonl').read_text().splitlines()]
 for x in rows:
  if x['dangling'] or x['duplicate_owners'] or not x['imports_match']:errors.append(x['module'])
 (D/'scan_summary.json').write_text(json.dumps(dict(modules=len(rows),declarations=sum(x['declarations'] for x in rows),edges=sum(x['edges'] for x in rows),errors=errors),indent=2))
 raw=(B/'NKJ_LOADED_scan.jsonl').read_bytes();(D/'NKJ_LOADED_scan.jsonl.xz').write_bytes(lzma.compress(raw,preset=6));(D/'NKJ_LOADED_scan.jsonl.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
out=dict(mode=mode,exit=r.returncode,roots=results,errors=errors,binary_sha256=hashlib.sha256((B/'NKJ_native/NKJ_Driver').read_bytes()).hexdigest())
(D/(mode+'.json')).write_text(json.dumps(out,indent=2));print(json.dumps(dict(mode=mode,exit=r.returncode,roots=len(results),errors=len(errors))))
raise SystemExit(r.returncode or bool(errors))
