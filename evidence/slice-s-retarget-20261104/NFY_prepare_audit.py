"""Admitted ax2 adaptation: root/module lists and runtime filenames only."""
from pathlib import Path
import json,re,hashlib,difflib
E=Path(__file__).resolve().parent;R=E.parents[1];P=E.parent/'ledger7-20261104'
p=json.loads((E/'NFY_PROVENANCE.json').read_text());ren=p['namespace_map']
pat=re.compile(r'(?<![A-Za-z0-9_])('+'|'.join(map(re.escape,sorted(ren,key=len,reverse=True)))+r')(?![A-Za-z0-9_])')
old=json.loads((E.parent/'slice-s-compose12-20261104/NFJ_AUDIT.json').read_text());sr=[pat.sub(lambda m:ren[m.group()],r['root']) for r in old['results']]
sr+=['NFY_NEE_M31SerializerDomain.'+n for n in ['primitive','width','widths_distinct']]
sr+=['NFY_NFD_WideSerialization.result_state_effects','NFY_NCA_SerializerWindow.frame','NFY_NCA_SerializerWindow.induction']
base=json.loads((P/'NFX_AUDIT_ROOTS.json').read_text());roots=sorted(set(base['roots']+sr));mods=['NFX_COMBINED_IMPORT']+[f'NFY_Part{i:03}' for i in range(len(p['groups']))]
combined=''.join('import '+m+'\n' for m in mods)+''.join('#print axioms '+n+'\n' for n in roots)
(E/'NFY_COMBINED_IMPORT.lean').write_text(combined)
groups=[roots[i:i+4] for i in range(0,len(roots),4)]
(E/'NFY_AUDIT_ROOTS.json').write_text(json.dumps(dict(headline=base['headline'],imports=mods,roots=roots,groups=groups,S_roots=sr),indent=1)+'\n')
source=(P/'NFX_ProofDriver.lean').read_text();a=source.index('  let (modules, roots) :=');b=source.index('  let env ← importModules',a)
choices=''.join(('    if' if i==0 else '    else if')+f' mode == "proof{i}" then\n      (#[`NFY_COMBINED_IMPORT], #['+', '.join('`'+x for x in rs)+'])\n' for i,rs in enumerate(groups))
fixture=source[source.index('    else if mode == "fixtures" then',a):b]
proof=source[:a]+'  let (modules, roots) :=\n'+choices+fixture+source[b:]
(E/'NFY_ProofDriver.lean').write_text(proof)
(E/'NFY_PROOF_DRIVER.diff').write_text(''.join(difflib.unified_diff(source.splitlines(True),proof.splitlines(True),fromfile='NFX_ProofDriver.lean',tofile='NFY_ProofDriver.lean')))
source=(P/'NFX_Driver.lean').read_text();scan=source.replace('NFX_COMBINED_IMPORT','NFY_COMBINED_IMPORT').replace('NFX_EXPECTED_IMPORTS','NFY_EXPECTED_IMPORTS').replace('NFX_LOADED_scan','NFY_LOADED_scan')
(E/'NFY_Driver.lean').write_text(scan)
(E/'NFY_SCANNER.diff').write_text(''.join(difflib.unified_diff(source.splitlines(True),scan.splitlines(True),fromfile='NFX_Driver.lean',tofile='NFY_Driver.lean')))
tables={r['module']:r['imports'] for r in map(json.loads,(P/'NFX_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
G=json.loads((E/'NFY_SOURCE_GRAPH.json').read_text())
for n,r in G.items():
 if n not in tables:tables[n]=list(dict.fromkeys(['Init']+r['imports']))
for f in E.glob('NFY_*.lean'):tables[f.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',f.read_text(),re.M)))
(E/'NFY_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=n,imports=im))+'\n' for n,im in sorted(tables.items())))
walker=(R/'evidence/axaudit2-20261102/NEP_WALKER.lean').read_bytes();other=(R/'evidence/slice-q-accum-20261104/NFS_native/NFA_WALKER.c')
(E/'NFY_WALKER_PIN.json').write_text(json.dumps(dict(sha256=hashlib.sha256(walker).hexdigest(),path='evidence/axaudit2-20261102/NEP_WALKER.lean',resolved_module='NFA_WALKER',inherited_pin=json.loads((P/'NFX_WALKER_PIN.json').read_text()),driver_pre_runtime_prefix_unchanged=proof[:a]==source[:a] if False else proof[:proof.index('  let (modules, roots) :=')]==(P/'NFX_ProofDriver.lean').read_text().split('  let (modules, roots) :=')[0]),indent=1)+'\n')
(E/'NFY_batch.py').write_text((P/'NFX_batch.py').read_text().replace('NFX_','NFY_'))
print(json.dumps(dict(roots=len(roots),s_roots=len(sr),parts=len(p['groups']),groups=len(groups))))
