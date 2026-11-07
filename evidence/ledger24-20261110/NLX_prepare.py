"""Owned ledger24 preparation; predecessors are read only."""
from pathlib import Path
import json,lzma,re,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'ledger23-20261110';Q=E.parent/'tx2-common2-20261110'
C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NLX_20261110'
def raw(p):
 if p.exists():return p.read_bytes()
 xp=Path(str(p)+'.xz')
 if xp.exists():
  b=lzma.decompress(xp.read_bytes());sp=Path(str(p)+'.sha256')
  if sp.exists():assert hashlib.sha256(b).hexdigest()==sp.read_text().strip()
  return b
 r=json.loads(Path(str(p)+'.ref.json').read_text());b=lzma.decompress((p.parent/r['owned_input']).read_bytes());assert hashlib.sha256(b).hexdigest()==r['sha256'];return b
J=lambda p:json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else raw(p))
roots=set();expected={};conflicts=[];seeds=[];extras=[]
for folder,pre,export_pre in [(P,'NLS','NLO'),(Q,'NLT','NLT')]:
 roots.update(J(folder/f'{pre}_AUDIT_ROOTS.json')['roots'])
 for l in raw(folder/f'{pre}_EXPECTED_IMPORTS.jsonl').decode().splitlines():
  x=json.loads(l);m=x['module'];v=x['imports']
  if m in expected and expected[m]!=v:conflicts.append(dict(module=m,earlier=expected[m],later=v,provider=pre))
  else:expected[m]=v
 x=J(folder/f'{export_pre}_EXPORT.json');base=x.get('export',x.get('path'));assert base
 for r in x['files']:
  src=r.get('path',base+'/'+r.get('name',''));assert src.startswith(base+'/')
  seeds.append(dict(tag=pre,path=src,relative=src[len(base)+1:],sha256=r['sha256'],bytes=r['bytes']))
 extras += [base]+(J(folder/'NLO_PATHS.json')if pre=='NLS'else J(folder/'NLT_PATHS.json'))
roots=sorted(roots)
for n,x in [('AUDIT_ROOTS',dict(roots=roots,groups=[roots[i*len(roots)//30:(i+1)*len(roots)//30]for i in range(30)])),('AUDIT_MODULES',[['NLX_COMBINED_IMPORT']for _ in range(30)]),('SEED_INPUTS',seeds),('PATHS',list(dict.fromkeys([C+'/NLS_seed',C+'/NLT_seed']+extras))),('EXPECTED_CONFLICTS',conflicts)]:
 (E/f'NLX_{n}.json').write_text(json.dumps(x,indent=1)+'\n')
(E/'NLX_COMBINED_IMPORT.lean').write_text('import NLS_COMBINED_IMPORT\nimport NLT_COMBINED_IMPORT\nimport RPx_Deployed\n#print axioms NLT_CompleteRoot.root\n#print axioms AspisR1.RPx_Deployed.deployed\n')
for name in ['Driver','ProofDriver','OwnerStatements']:
 p=E/f'NLX_{name}.lean'
 if not p.exists():p.write_text((P/f'NLS_{name}.lean').read_text().replace('NLS_','NLX_'))
for name in ['run','batch','setup','pin','scope40','hygiene']:
 s=(P/f'NLS_{name}.py').read_text().replace('NLS_','NLX_').replace('codex-cx-ledger23-20261110','codex-cx-ledger24-20261110')
 s=s.replace("E.parent/'ledger22-20261110/NLO_CLOSURE_PINS.json.xz'","E.parent/'ledger23-20261110/NLS_CLOSURE_PINS.json.xz'")
 p=E/f'NLX_{name}.py'
 if not p.exists():p.write_text(s)
# Scope8 prints the exact complete candidate statement and definition inventory.
s='import NLX_COMBINED_IMPORT\nset_option pp.proofs false\n'
for n in ['NLT_CompleteRoot.root','NLT_CompleteRoot.RowSpec','NLT_CompleteRoot.Native','NLT_CompleteRoot.Law','NLT_CompleteRoot.ResolvedLaw','NLT_CompleteRoot.StoppedLaw','NLT_CompleteRoot.CallLaw','NLT_C04Stop.Cut','NLT_C04Stop.At','NLT_NativeInvocation.Occurrence','NLT_NativeInvocation.Invocation','NLT_NativeWindows.Input','NLT_NativeInvocation.Detail']:
 s+='#print '+n+'\n'
s+='#print axioms NLT_CompleteRoot.root\n'
p=E/'NLX_HypothesisReview.lean'
if not p.exists():p.write_text(s)
for p in E.glob('NLX_*.lean'):expected[p.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)))
(E/'NLX_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n'for m,v in sorted(expected.items())))
assert not conflicts,conflicts
print(json.dumps(dict(roots=len(roots),seeds=len(seeds),conflicts=len(conflicts))))
