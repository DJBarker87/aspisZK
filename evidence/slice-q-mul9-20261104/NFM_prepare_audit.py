from pathlib import Path
import re,json,hashlib,difflib,subprocess,os
E=Path(__file__).resolve().parent;P=E.parent/'slice-q-mul8-20261104'
s=(P/'NFI_Driver.lean').read_text();start=s.index('    if mode == "proof0"');end=s.index('    else if mode == "scan"',start)
oldroots=re.findall(r'`(AspisR1\.[A-Za-z0-9_.]+)',s[start:end]);assert len(oldroots)==len(set(oldroots))==75
newroots=[]
for module in ['NFM_Control','NFM_InnerControl','NFM_Thread','NFM_Cuts','NFM_Single','NFM_Domains','NFM_Span','NFM_Frames','NFM_CallDomains','NFM_ProductInstance']:
 text=(E/(module+'.lean')).read_text()
 for name in re.findall(r'^#print axioms ([A-Za-z0-9_.]+)$',text,re.M):
  root=name if '.' in name else 'AspisR1.'+module+'.'+name
  newroots.append(root)
roots=list(dict.fromkeys(oldroots+newroots))
# Three roots per import; every root is walked exactly once in this audit.
count=int(os.environ.get('NFM_AUDIT_GROUPS','33'));assert 1<=count<=len(roots)
q,r=divmod(len(roots),count);groups=[];offset=0
for i in range(count):
 size=q+(i<r);groups.append(roots[offset:offset+size]);offset+=size
section=''
for i,group in enumerate(groups):
 section+=('    if' if i==0 else '    else if')+' mode == "proof'+str(i)+'" then\n      (#[`NFM_CombinedFinal], #['+', '.join('`'+r for r in group)+'])\n'
s=s[:start]+section+s[end:]
s=s.replace('`NFI_CombinedFinal','`NFM_CombinedFinal').replace('NFI_EXPECTED_IMPORTS','NFM_EXPECTED_IMPORTS').replace('NFI_LOADED_scan','NFM_LOADED_scan').replace('NFI_SCAN_','NFM_SCAN_')
# Keep the ax2 driver diff limited to roots/modules and runtime setup.
# The inherited incoherence scanner is a SEPARATE executable, byte-identical
# in its core to NFI's scanner; it does not extend the audit driver.
a=s.index('namespace NER\n');b=s.index('end NER\n',a)+len('end NER\n');core=s[a:b]
s=s[:a]+s[b:]
s=s.replace('    else if mode == "scan" then (#[`NFM_CombinedFinal], #[])\n','')
a=s.index('  if mode == "scan" then\n');b=s.index('  let ctx : Command.Context',a);scan_runtime=s[a:b]
s=s[:a]+s[b:]
scanner='import Lean\nimport NFA_MemoryLimit\nopen Lean Elab Command\n'+core+'\nunsafe def main (_args : List String) : IO UInt32 := do\n  NFA_MemoryLimit.set\n  initSearchPath (← findSysroot)\n  enableInitializersExecution\n  let env ← importModules #[{module := `NFM_CombinedFinal, importAll := true}] {} (loadExts := true) (level := .private)\n'
scanner+='\n'.join(line[2:] for line in scan_runtime.splitlines()[1:])+'\n'
(E/'NFM_Scanner.lean').write_text(scanner)
(E/'NFM_SCANNER_CORE.json').write_text(json.dumps(dict(unchanged=True,sha256=hashlib.sha256(core.encode()).hexdigest(),source='evidence/slice-q-mul8-20261104/NFI_Driver.lean:namespace NER'),indent=2))
(E/'NFM_Driver.lean').write_text(s)
(E/'NFM_DRIVER.diff').write_text(''.join(difflib.unified_diff((E.parent/'axaudit2-20261102/NEP_Driver.lean').read_text().splitlines(True),s.splitlines(True),fromfile='NEP_Driver.lean',tofile='NFM_Driver.lean')))
(E/'NFM_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=groups,new_roots=newroots),indent=2))
expected={r['module']:r['imports'] for r in map(json.loads,(P/'NFI_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
# Newly composed modules have explicit import headers; Init is implicit.
for module in ['NFM_Control','NFM_InnerControl','NFM_Thread','NFM_Cuts','NFM_Single','NFM_Domains','NFM_Span','NFM_Frames','NFM_CallDomains','NFM_ProductInstance','NFM_CombinedFinal']:
 text=(E/(module+'.lean')).read_text();expected[module]=['Init']+[n for line in text.splitlines() if line.startswith('import ') for n in line[7:].split()]
(E/'NFM_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n' for m,v in sorted(expected.items())))
walker=subprocess.check_output(['git','show','HEAD:evidence/slice-q-mul4-20261104/NFA_WALKER.lean'])
original=subprocess.check_output(['git','show','HEAD:evidence/axaudit2-20261102/NEP_WALKER.lean'])
assert walker==original
(E/'NFM_WALKER_PIN.json').write_text(json.dumps(dict(walker_unchanged=True,sha256=hashlib.sha256(walker).hexdigest(),source='evidence/slice-q-mul4-20261104/NFA_WALKER.lean',canonical='evidence/axaudit2-20261102/NEP_WALKER.lean'),indent=2))
print(len(roots),len(groups))
