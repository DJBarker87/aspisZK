"""Own proof-audit inputs, with unchanged ax2 action/walker and scanner core."""
from pathlib import Path
import json,hashlib,re,subprocess,difflib
E=Path(__file__).resolve().parent;P=E.parent/'slice-q-mul9-20261104'
sha=lambda b:hashlib.sha256(b).hexdigest()
# Only successfully checked source modules enter the accepted support forest.
rows=[json.loads(l) for l in (E/'NFP_ATTEMPTS.jsonl').read_text().splitlines()]
valid={}
for r in rows:
 if r['kind']=='lean' and r['exit_status']==0 and r['module'].startswith('NFP_') and r['module'] not in ['NFP_CombinedFinal','NFP_Driver','NFP_Scanner']:
  p=E/(r['module']+'.lean')
  if p.is_file() and r['source_hashes']['NFP_generated/'+r['module']+'.lean']==sha(p.read_bytes()):valid[r['module']]=r
mods=sorted(valid);roots=[]
for m in mods:
 for n in re.findall(r'^#print axioms ([A-Za-z0-9_.]+)$',(E/(m+'.lean')).read_text(),re.M):
  roots.append(n if '.' in n else 'AspisR1.'+m+'.'+n)
old=['AspisR1.RPx_Deployed.deployed','AspisR1.NFM_ProductInstance.installed','AspisR1.NFM_ProductInstance.wrapper','AspisR1.NFM_Cuts.abort_prefix','AspisR1.NFG_QueryLoopSource.complete','AspisR1.NFG_PushRoot.private_result','AspisR1.NFG_PushRoot.public_result']
roots=list(dict.fromkeys(roots+old));count=7;q,r=divmod(len(roots),count);groups=[];offset=0
for i in range(count):
 size=q+(i<r);groups.append(roots[offset:offset+size]);offset+=size
combined=''.join('import '+m+'\n' for m in ['NFM_CombinedFinal','NFG_RootsCombined']+mods)
combined+='\n'+''.join('#print axioms '+n+'\n' for n in roots)
(E/'NFP_CombinedFinal.lean').write_text(combined)
s=(P/'NFM_Driver.lean').read_text();a=s.index('    if mode == "proof0"');b=s.index('    else if mode == "fixtures"',a)
section=''
for i,g in enumerate(groups):section+=('    if' if i==0 else '    else if')+' mode == "proof'+str(i)+'" then\n      (#[`NFP_CombinedFinal], #['+', '.join('`'+n for n in g)+'])\n'
section += '    else if mode == \"extra\" then\n      (#[`NFP_CombinedFinal], #[`AspisR1.NFM_Single.domains, `AspisR1.NFG_PushRoot.private_domains])\n'
s=s[:a]+section+s[b:]
canonical=(E.parent/'axaudit2-20261102/NEP_Driver.lean').read_text()
assert s[s.index('  let env ← importModules'):]==canonical[canonical.index('  let env ← importModules'):]
(E/'NFP_Driver.lean').write_text(s)
(E/'NFP_DRIVER.diff').write_text(''.join(difflib.unified_diff(canonical.splitlines(True),s.splitlines(True),fromfile='NEP_Driver.lean',tofile='NFP_Driver.lean')))
scanner=(P/'NFM_Scanner.lean').read_text();a=scanner.index('namespace NER\n');b=scanner.index('end NER\n',a)+len('end NER\n')
core=scanner[a:b];assert sha(core.encode())==json.loads((P/'NFM_SCANNER_CORE.json').read_text())['sha256']
scanner=scanner.replace('NFM_CombinedFinal','NFP_CombinedFinal').replace('NFM_EXPECTED_IMPORTS','NFP_EXPECTED_IMPORTS').replace('NFM_LOADED_scan','NFP_LOADED_scan').replace('NFM_SCAN_','NFP_SCAN_')
(E/'NFP_Scanner.lean').write_text(scanner)
walker=subprocess.check_output(['git','show','HEAD:evidence/slice-q-mul4-20261104/NFA_WALKER.lean']);orig=(E.parent/'axaudit2-20261102/NEP_WALKER.lean').read_bytes();assert walker==orig
(E/'NFP_WALKER_PIN.json').write_text(json.dumps(dict(unchanged=True,sha256=sha(orig),scanner_core_sha256=sha(core.encode())),indent=2)+'\n')
(E/'NFP_AUDIT_ROOTS.json').write_text(json.dumps(dict(modules=mods,roots=roots,groups=groups),indent=2)+'\n')
# Independent expected import tables are parsed from committed sources;
# any actual object/source mismatch remains a hard scanner failure.
expected={r['module']:r['imports'] for r in map(json.loads,(P/'NFM_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
paths=subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD'],text=True).splitlines();leanpaths=[p for p in paths if p.endswith('.lean')]
source_pins={};pending=['NFP_CombinedFinal']
while pending:
 m=pending.pop()
 if m in expected:continue
 own=E/(m+'.lean')
 if own.is_file():text=own.read_text();path=str(own)
 else:
  tail=m.replace('.','/')+'.lean';candidates=[p for p in leanpaths if p.endswith('/'+tail) or p==tail]
  # Prefer canonical repository sources, then committed public lane modules.
  candidates.sort(key=lambda p:(0 if p=='docs/research/100bit-spend-path-20261013/lean/'+tail else 1 if p=='lean/'+tail else 2 if p.startswith('evidence/slice-q-compose6-20261104/') and '/sources/' not in p else 3 if '/sources/' not in p else 4,len(p),p))
  assert candidates,('No independent expected imports for',m)
  path=candidates[0];text=subprocess.check_output(['git','show','HEAD:'+path],text=True)
 imports=['Init']+[n for line in text.splitlines() if line.startswith('import ') for n in line[7:].split() if n!='all']
 expected[m]=list(dict.fromkeys(imports));source_pins[m]=dict(path=path,sha256=sha(text.encode()),imports=imports)
 pending+=imports
(E/'NFP_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=i))+'\n' for m,i in sorted(expected.items())))
(E/'NFP_EXPECTED_SOURCE_PINS.json').write_text(json.dumps(source_pins,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),roots=len(roots),groups=len(groups),expected_modules=len(expected),new_import_sources=len(source_pins))))
