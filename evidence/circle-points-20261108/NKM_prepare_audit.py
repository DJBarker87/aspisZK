from pathlib import Path
import json,re,subprocess,hashlib,difflib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-circle-points-20261108';P=E.parent/'ledger18-20261108'
roots=[]
for p in sorted(E.glob('NKM_*.lean'))+list((E/'NKM_generated/NKM_circle').glob('FunsExternal.lean')):
 s=p.read_text();m=re.search(r'^namespace ([\w.]+)',s,re.M)
 if not m:continue
 ns=m[1]
 for r in re.findall(r'^#print axioms ([\w.]+)',s,re.M):
  full=r if r.startswith(ns+'.') else ns+'.'+r
  if full not in roots:roots.append(full)
headline='AspisR1.RPx_Deployed.deployed'
combined='import NKH_COMBINED_IMPORT\nimport NKM_Adopted\nimport NKM_SpecLaws\nimport NKM_NaturalLaws\nimport NKM_SpecMatching\nimport NKM_EmittedMul\nimport NKM_FallbackTrace\n#print axioms '+headline+'\n'
(E/'NKM_COMBINED_IMPORT.lean').write_text(combined);(E/'NKM_generated/NKM_COMBINED_IMPORT.lean').write_text(combined)
(E/'NKM_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots+[headline],groups=[roots,[headline]]),indent=2)+'\n')
(E/'NKM_AUDIT_MODULES.json').write_text(json.dumps([['NKM_COMBINED_IMPORT'],['NKM_COMBINED_IMPORT']]))
review='import NKM_COMBINED_IMPORT\n'+''.join('#check '+r+'\n#print '+r+'\n'for r in ['NKM_Roots.circle','NKM_Roots.ood','NKM_Roots.fallback','NKM_CircleModel.circle_source','NKM_Adopted.ood','NKM_Adopted.fallback'])
(E/'NKM_Review.lean').write_text(review);(E/'NKM_generated/NKM_Review.lean').write_text(review)
for name in ['Driver','ProofDriver']:
 raw=(P/('NKH_'+name+'.lean')).read_text();s=raw.replace('NKH_','NKM_');(E/'NKM_generated'/('NKM_'+name+'.lean')).write_text(s)
 (E/('NKM_'+name+'.diff')).write_text(''.join(difflib.unified_diff(raw.splitlines(True),s.splitlines(True),fromfile='NKH_'+name,tofile='NKM_'+name)))
(E/'NKM_inputs').mkdir(exist_ok=True);pins=[]
for n in ['NFA_WALKER','NFA_MemoryLimit']:
 rel='evidence/slice-q-mul4-20261104/'+n+'.lean';raw=subprocess.check_output(['git','show','HEAD:'+rel]);(E/'NKM_inputs'/(n+'.lean')).write_bytes(raw);pins.append(dict(path=rel,sha256=hashlib.sha256(raw).hexdigest(),copied_unchanged=True))
walker=Path('evidence/axaudit2-20261102/NEP_WALKER.lean').read_bytes();assert walker==(E/'NKM_inputs/NFA_WALKER.lean').read_bytes()
(E/'NKM_TOOL_INPUT_PINS.json').write_text(json.dumps(dict(pins=pins,NEP_walker_byte_identical=True),indent=2)+'\n')
expected={r['module']:r['imports']for r in map(json.loads,(P/'NKH_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
for p in(E/'NKM_generated').rglob('*.lean'):
 m=str(p.relative_to(E/'NKM_generated'))[:-5].replace('/','.')
 expected[m]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)))
(E/'NKM_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=xs))+'\n'for m,xs in sorted(expected.items())))
base=json.loads((E/'NKM_L018.json').read_text());base.pop('deps_fingerprint',None)
base['env']['LEAN_PATH']=base['env']['LEAN_PATH'].replace('/NKM_seed/NKH:', '/NKM_seed/NKH_seed:')
def lean(i,m,source,codegen=False):
 x=json.loads(json.dumps(base));x.update(attempt=f'NKM_L{i:03}',module=m,sources=[source],expected_time='One focused Lean module; audit source unchanged except roots and paths')
 x['command']=[x['env']['LEAN_SYSROOT']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R',str(Path(source).parent),source]
 if source.startswith('NKM_generated/'):x['command']+=['-o','NKM_objects/'+m+'.olean']
 if codegen:x['command']+=['-c','NKM_native/'+m+'.c']
 (E/(x['attempt']+'.json')).write_text(json.dumps(x))
lean(23,'NKM_COMBINED_IMPORT','NKM_generated/NKM_COMBINED_IMPORT.lean');lean(24,'NKM_Review','NKM_generated/NKM_Review.lean')
lean(25,'NFA_WALKER','NKM_inputs/NFA_WALKER.lean',True);lean(26,'NFA_MemoryLimit','NKM_inputs/NFA_MemoryLimit.lean',True)
lean(27,'NKM_Driver','NKM_generated/NKM_Driver.lean',True);lean(28,'NKM_ProofDriver','NKM_generated/NKM_ProofDriver.lean',True)
for i,n in [(29,'Driver'),(30,'ProofDriver')]:
 x=json.loads(json.dumps(base));x.update(attempt=f'NKM_L{i:03}',kind='link',module='NKM_'+n,sources=['NKM_native/NKM_'+n+'.c','NKM_native/NFA_WALKER.c','NKM_native/NFA_MemoryLimit.c'],command=[base['env']['LEAN_SYSROOT']+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NKM_native/NKM_'+n,'NKM_native/NKM_'+n+'.c','NKM_native/NFA_WALKER.c','NKM_native/NFA_MemoryLimit.c'],expected_time='Optimized linking of unchanged audit tooling');(E/(x['attempt']+'.json')).write_text(json.dumps(x))
for i,mode,driver in [(31,'fixtures','ProofDriver'),(32,'scan','Driver'),(33,'proof0','ProofDriver'),(34,'proof1','ProofDriver')]:
 x=json.loads(json.dumps(base));x.update(attempt=f'NKM_L{i:03}',kind='audit',module=mode,sources=['NKM_AUDIT_ROOTS.json','NKM_AUDIT_MODULES.json','NKM_EXPECTED_IMPORTS.jsonl'],command=['NKM_native/NKM_'+driver,mode],collect_globs=['NEP_'+mode+'_*'],collect=['NKM_LOADED_scan.jsonl']if mode=='scan'else[],expected_time='One combined-cohort NFX scan / hardened raw ax2 traversal, no source replay');(E/(x['attempt']+'.json')).write_text(json.dumps(x))
print('Prepared one combined audit:',len(roots),'own theorem roots and headline')
