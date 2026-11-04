"""Adapt only ax2 driver root/module lists; preserve the hardened walker."""
from pathlib import Path
import json,re,hashlib,difflib
E=Path(__file__).resolve().parent;O=E.parent/'pool-retdata-20261104'
roots=[];modules=[];matches=[]
for p in sorted(E.glob('NFR_*.lean')):
 if p.stem in ['NFR_Driver','NFR_Coherence','NFR_WALKER']:continue
 source=p.read_text();printed=re.findall(r'^#print axioms ([\w.]+)',source,re.M)
 if not printed:continue
 sha=hashlib.sha256(p.read_bytes()).hexdigest()
 receipts=[]
 for r in E.glob('NFR_*/receipt.json'):
  d=json.loads(r.read_text())
  if d.get('module')==p.stem and d.get('exit_status')==0 and sha in d.get('source_hashes',{}).values():receipts.append(str(r.relative_to(E)))
 assert receipts,(p.name,'source not compiled')
 ns=re.findall(r'^namespace ([\w.]+)',source,re.M)[0]
 names=[n if n.startswith(ns+'.') else ns+'.'+n for n in printed]
 roots.extend(names);modules.append(p.stem);matches.append(dict(module=p.stem,sha256=sha,receipts=receipts,roots=names))
s=(O/'NFO_Driver.lean').read_text();a=s.index('    (#[`NFO_Final],');b=s.index('    else if mode == "fixtures"',a)
s=s[:a]+'    (#['+','.join('`'+m for m in modules)+'],\n     #['+','.join('`'+r for r in roots)+'])\n'+s[b:]
# No walker/adaptation changes; labels retained deliberately for direct diff.
(E/'NFR_Driver.lean').write_text(s)
(E/'NFR_DRIVER.diff').write_text(''.join(difflib.unified_diff((O/'NFO_Driver.lean').read_text().splitlines(True),s.splitlines(True),fromfile='NFO_Driver.lean',tofile='NFR_Driver.lean')))
walker=(O/'NFO_WALKER.lean').read_bytes();canonical=(E.parent/'axaudit2-20261102/NEP_WALKER.lean').read_bytes();assert walker==canonical
(E/'NFR_AUDIT_INPUTS.json').write_text(json.dumps(dict(modules=modules,roots=roots,sources=matches,walker_sha256=hashlib.sha256(walker).hexdigest(),walker_identical=True,driver_diff='NFR_DRIVER.diff',retained_walker='evidence/pool-retdata-20261104/NFO_WALKER.lean'),indent=1)+'\n')
# Existing exhaustive loaded-environment scanner; only new module list/output label.
s=(O/'NFO_Coherence.lean').read_text().replace('namespace NFO_Coherence','namespace NFR_Coherence').replace('end NFO_Coherence','end NFR_Coherence').replace('NFO_Coherence.referenceNames','NFR_Coherence.referenceNames').replace('NFO_LOADED.jsonl','NFR_LOADED.jsonl').replace('#[{module := `NFO_Final, importAll := true}]','[') if False else (O/'NFO_Coherence.lean').read_text()
s=s.replace('namespace NFO_Coherence','namespace NFR_Coherence').replace('end NFO_Coherence','end NFR_Coherence').replace('NFO_Coherence.referenceNames','NFR_Coherence.referenceNames').replace('NFO_LOADED.jsonl','NFR_LOADED.jsonl')
s=s.replace('#[{module := `NFO_Final, importAll := true}]', '#['+','.join('{module := `'+m+', importAll := true}' for m in modules)+']').replace('loaded NFO closure','loaded NFR closure')
(E/'NFR_Coherence.lean').write_text(s)
print(len(modules),'modules',len(roots),'roots')
