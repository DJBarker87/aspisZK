from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'ledger28-20261111';H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):
 if p.exists():return p.read_bytes()
 b=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(b)==Path(str(p)+'.sha256').read_text().strip();return b
def put(n,x):
 b=(json.dumps(x,indent=1)+'\n').encode();p=E/('NNM_'+n+'.json')
 if len(b)>20_000_000:Path(str(p)+'.xz').write_bytes(lzma.compress(b));Path(str(p)+'.sha256').write_text(H(b)+'\n')
 else:p.write_bytes(b)
s={}
for l in raw(E/'NNM_L026/stdout.log').decode().splitlines():
 if 'NNM_OWNER 'in l:
  r=json.loads(l.split('NNM_OWNER ',1)[1]);assert r['root']not in s;s[r['root']]=r
assert set(s)==set(json.loads((E/'NNM_AUDIT_ROOTS.json').read_text())['roots'])
prior=json.loads(lzma.decompress((P/'NNL_KERNEL_STATEMENTS.json.xz').read_bytes()));differences=[]
for root,r in prior.items():
 if s[root]!=r:differences.append(dict(root=root,previous=r,current=s[root]))
put('KERNEL_STATEMENTS',s);put('STATEMENT_COMPARISON',dict(status='PASS'if not differences else'FAIL',predecessor_roots=len(prior),current_roots=len(s),differences=differences));assert not differences,len(differences)
print('NNM complete statements PASS; all predecessor root types/owners identical')
