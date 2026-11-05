from pathlib import Path
import json,re,hashlib,subprocess,sys
E=Path(__file__).resolve().parent;R=E.parents[1];H=lambda b:hashlib.sha256(b).hexdigest()
mods=json.loads((E/'NIM_AFFECTED.json').read_text());mp={m:'NIM_'+m for m in mods}
# Keep every nonshared owner name exactly; module identity changes do not rename declarations.
mp['NGL_MapReference.Types']='NIM_MapReference.Types';mp['NGL_MapReference.Funs']='NIM_MapReference.Funs'
paths={}
for d in ['slice-d-entry-20261105','slice-d-entry2-20261106','slice-d-entry3-20261106','slice-d-entry4-20261106']:
 for p in (E.parent/d).glob('*.lean'):paths[p.stem]=p
paths['NGL_MapReference.Types']=E.parent/'slice-d-entry-20261105/NGL_extracted/NGL_MapReference/NGL_MapReference/Types.lean'
paths['NGL_MapReference.Funs']=E.parent/'slice-d-entry-20261105/NGL_MapCanonicalFuns.lean'
paths['NGL_MapReference.Types']=E.parent/'slice-d-entry-20261105/NGL_MapCanonicalTypes.lean'
nfw=(E.parent/'slice-d-prepare-20261104/NFW_ErrorReferenceTypes.lean').read_text()
ngl=paths['NGL_MapReference.Types'].read_text()
pat=r'@\[discriminant isize\]\ninductive VerifierError where\n(?:\|[^\n]*\n)+'
a=re.search(pat,nfw);b=re.search(pat,ngl);assert a and b and a[0]==b[0]
pro=[];texts={}
for m in mods:
 p=paths[m];s=p.read_text();out=s
 # Import replacement only; no namespace or theorem rename. Old modules cannot coexist with retargeted copies.
 out=re.sub(r'^import ([\w.]+)',lambda x:'import '+mp.get(x[1],x[1]),out,flags=re.M)
 if m=='NGL_MapReference.Types':
  out=out.replace('import Aeneas','import Aeneas\nimport NFW_ErrorReferenceTypes')
  out=re.sub(r'/-- \[ngl_reference::VerifierError\][\s\S]*?(?=end NGL_MapReference)','',out)
 if m in ['NGL_MapReference.Funs','NGL_MapReferenceModel']:
  out=out.replace('NGL_MapReference.VerifierError','NFW_ErrorReference.VerifierError')
  if m.endswith('.Funs'):out=re.sub(r'\bVerifierError\b','NFW_ErrorReference.VerifierError',out)
 texts[m]=out
 q=E/(mp[m]+'.lean')
 if '--check' in sys.argv:assert q.read_text()==out, q
 else:q.write_text(out)
 pro.append(dict(original_module=m,module=mp[m],source=str(p.relative_to(R)),source_sha256=H(s.encode()),source_lines=[1,len(s.splitlines())],output=q.name,sha256=H(out.encode()),changes='imports only' if out==re.sub(r'^import ([\w.]+)',lambda x:'import '+mp.get(x[1],x[1]),s,flags=re.M) else 'remove shared VerifierError owner; qualify uses to canonical NFW_ErrorReference.VerifierError; import retargets'))
order=[]
def visit(m):
 if m in order:return
 for i in re.findall(r'^import ([\w.]+)',paths[m].read_text(),re.M):
  if i in mp:visit(i)
 order.append(m)
for m in mods:visit(m)
if '--check' in sys.argv:
 print('deterministic body/import check PASS');sys.exit(0)
(E/'NIM_PROVENANCE.json').write_text(json.dumps(dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),module_map=mp,order=[mp[m]for m in order],modules=pro,shared_inductive=dict(nfw_lines=[nfw[:a.start()].count('\n')+1,nfw[:a.end()].count('\n')],ngl_lines=[ngl[:b.start()].count('\n')+1,ngl[:b.end()].count('\n')],sha256=H(a[0].encode()),byte_identical=True)),indent=1)+'\n')
s=(E.parent/'ledger11-20261107/NII_COMBINED_IMPORT.lean').read_text()
s=re.sub(r'^import ([\w.]+)',lambda x:'import '+mp.get(x[1],x[1]),s,flags=re.M)
s='import '+mp['NHY_COMBINED_IMPORT']+'\n'+s
(E/'NIM_COMBINED_IMPORT.lean').write_text(s)
print(json.dumps(dict(count=len(order),order=[mp[m]for m in order])))
