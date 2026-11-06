"""Adapt only roots, imports and paths; raw walker and scanner checks unchanged."""
from pathlib import Path
import json,re,subprocess,hashlib,difflib
E=Path(__file__).resolve().parent;P=E.parent/'ledger17-20261108'
mods=['NKD_Decode','NKD_Low','NKD_Add','NKD_Ordinary','NKD_Gamma','NKD_Absorb','NKD_Block','NKD_New','NKD_Runtime','NKD_Values']
roots=['AspisR1.RPx_Deployed.deployed']+['AspisR1.'+m+'.root'for m in mods[:8]]+['AspisR1.NKD_Runtime.'+n+'_root'for n in ['new','absorb','block']]+['AspisR1.NKD_Values.gamma','AspisR1.NKD_Values.gamma_unique']
combined='import NKC_COMBINED_IMPORT\n'+''.join('import '+m+'\n'for m in mods)+'\n'+''.join('#print axioms '+r+'\n'for r in roots)
(E/'NKD_COMBINED_IMPORT.lean').write_text(combined);(E/'NKD_generated/NKD_COMBINED_IMPORT.lean').write_text(combined)
(E/'NKD_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=[roots]),indent=1)+'\n')
(E/'NKD_AUDIT_MODULES.json').write_text(json.dumps([['NKD_COMBINED_IMPORT']],indent=1)+'\n')
for name in ['Driver','ProofDriver']:
 raw=(P/('NKC_'+name+'.lean')).read_text();s=raw.replace('NKC_','NKD_');(E/'NKD_generated'/('NKD_'+name+'.lean')).write_text(s)
 (E/('NKD_'+name+'.diff')).write_text(''.join(difflib.unified_diff(raw.splitlines(True),s.splitlines(True),fromfile='NKC_'+name,tofile='NKD_'+name)))
# Private rebuild of unchanged tool modules, outside own selected module search path.
pins=[];(E/'NKD_inputs').mkdir(exist_ok=True)
for n in ['NFA_WALKER','NFA_MemoryLimit']:
 rel='evidence/slice-q-mul4-20261104/'+n+'.lean';raw=subprocess.check_output(['git','show','HEAD:'+rel]);(E/'NKD_inputs'/(n+'.lean')).write_bytes(raw);pins.append(dict(path=rel,sha256=hashlib.sha256(raw).hexdigest(),copied_unchanged=True))
(E/'NKD_TOOL_INPUT_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
expected={r['module']:r['imports']for r in map(json.loads,(P/'NKC_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
for p in(E/'NKD_generated').glob('NKD_*.lean'):expected[p.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)))
(E/'NKD_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=xs))+'\n'for m,xs in sorted(expected.items())))
base=json.loads((E/'NKD_L009.json').read_text());base.pop('deps_fingerprint',None)
def lean(i,m,source,codegen=False):
 x=dict(base,attempt=f'NKD_L{i:03}',module=m,sources=[source],expected_time='One focused Lean module; unchanged audit tool source where stated')
 root=str(Path(source).parent);x['command']=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R',root,source]
 if source.startswith('NKD_generated/'):x['command']+=['-o','NKD_objects/'+m+'.olean']
 if codegen:x['command']+=['-c','NKD_native/'+m+'.c']
 (E/(x['attempt']+'.json')).write_text(json.dumps(x,indent=1)+'\n')
lean(13,'NKD_Values','NKD_generated/NKD_Values.lean')
lean(14,'NKD_COMBINED_IMPORT','NKD_generated/NKD_COMBINED_IMPORT.lean')
lean(15,'NFA_WALKER','NKD_inputs/NFA_WALKER.lean',True)
lean(16,'NFA_MemoryLimit','NKD_inputs/NFA_MemoryLimit.lean',True)
lean(17,'NKD_Driver','NKD_generated/NKD_Driver.lean',True)
lean(18,'NKD_ProofDriver','NKD_generated/NKD_ProofDriver.lean',True)
for i,n in [(19,'Driver'),(20,'ProofDriver')]:
 x=dict(base,attempt=f'NKD_L{i:03}',kind='link',module='NKD_'+n,sources=['NKD_native/NKD_'+n+'.c','NKD_native/NFA_WALKER.c','NKD_native/NFA_MemoryLimit.c'],command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','leanc','-O3','-rdynamic','-o','NKD_native/NKD_'+n,'NKD_native/NKD_'+n+'.c','NKD_native/NFA_WALKER.c','NKD_native/NFA_MemoryLimit.c'],timeout=180,expected_time='Optimized linking of audit tools; no Rust arithmetic')
 (E/(x['attempt']+'.json')).write_text(json.dumps(x,indent=1)+'\n')
print('Prepared combined import, raw ax2 and unchanged NFX scanner inputs')
