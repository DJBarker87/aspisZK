from pathlib import Path
import re,json,hashlib,difflib,subprocess
E=Path(__file__).resolve().parent;P=E.parent/'slice-q-mul8-20261104'
s=(P/'NFI_Driver.lean').read_text();start=s.index('    if mode == "proof0"');end=s.index('    else if mode == "scan"',start)
oldroots=re.findall(r'`(AspisR1\.[A-Za-z0-9_.]+)',s[start:end]);assert len(oldroots)==len(set(oldroots))==75
newroots=[]
for module in ['NFM_Control','NFM_InnerControl','NFM_Thread','NFM_Cuts','NFM_Single','NFM_Domains','NFM_Span']:
 text=(E/(module+'.lean')).read_text()
 for name in re.findall(r'^#print axioms ([A-Za-z0-9_.]+)$',text,re.M):
  root=name if '.' in name else 'AspisR1.'+module+'.'+name
  newroots.append(root)
roots=list(dict.fromkeys(oldroots+newroots))
# Three roots per import; every root is walked exactly once in this audit.
groups=[roots[i:i+3] for i in range(0,len(roots),3)]
section=''
for i,group in enumerate(groups):
 section+=('    if' if i==0 else '    else if')+' mode == "proof'+str(i)+'" then\n      (#[`NFM_CombinedFinal], #['+', '.join('`'+r for r in group)+'])\n'
s=s[:start]+section+s[end:]
s=s.replace('`NFI_CombinedFinal','`NFM_CombinedFinal').replace('NFI_EXPECTED_IMPORTS','NFM_EXPECTED_IMPORTS').replace('NFI_LOADED_scan','NFM_LOADED_scan').replace('NFI_SCAN_','NFM_SCAN_')
(E/'NFM_Driver.lean').write_text(s)
(E/'NFM_DRIVER.diff').write_text(''.join(difflib.unified_diff((E.parent/'axaudit2-20261102/NEP_Driver.lean').read_text().splitlines(True),s.splitlines(True),fromfile='NEP_Driver.lean',tofile='NFM_Driver.lean')))
(E/'NFM_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=groups,new_roots=newroots),indent=2))
expected={r['module']:r['imports'] for r in map(json.loads,(P/'NFI_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
# Newly composed modules have explicit import headers; Init is implicit.
for module in ['NFM_Control','NFM_InnerControl','NFM_Thread','NFM_Cuts','NFM_Single','NFM_Domains','NFM_Span','NFM_CombinedFinal']:
 text=(E/(module+'.lean')).read_text();expected[module]=['Init']+[n for line in text.splitlines() if line.startswith('import ') for n in line[7:].split()]
(E/'NFM_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n' for m,v in sorted(expected.items())))
walker=subprocess.check_output(['git','show','HEAD:evidence/slice-q-mul4-20261104/NFA_WALKER.lean'])
original=subprocess.check_output(['git','show','HEAD:evidence/axaudit2-20261102/NEP_WALKER.lean'])
assert walker==original
(E/'NFM_WALKER_PIN.json').write_text(json.dumps(dict(walker_unchanged=True,sha256=hashlib.sha256(walker).hexdigest(),source='evidence/slice-q-mul4-20261104/NFA_WALKER.lean',canonical='evidence/axaudit2-20261102/NEP_WALKER.lean'),indent=2))
print(len(roots),len(groups))
