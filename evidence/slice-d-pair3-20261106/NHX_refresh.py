from pathlib import Path
import json,re
E=Path(__file__).resolve().parent;B=E.parent/'slice-d-pair2-20261106'
mods=sorted(p.stem for p in E.glob('NHX_*.lean')if p.stem not in ['NHX_COMBINED_IMPORT','NHX_Driver','NHX_ProofDriver','NHX_FINAL_STATEMENTS'])
s='import NGK_COMBINED_IMPORT\nimport NHM_COMBINED_IMPORT\n'+''.join('import '+m+'\n'for m in mods)+'set_option autoImplicit false\n#check AspisR1.RPx_Deployed.deployed\n#print axioms AspisR1.RPx_Deployed.deployed\n'
(E/'NHX_COMBINED_IMPORT.lean').write_text(s)
base=json.loads((B/'NHM_AUDIT_ROOTS.json').read_text());roots=[r for g in base['groups']for r in g]
for module in mods:
 text=(E/(module+'.lean')).read_text();ns=re.search(r'^namespace ([\w.]+)',text,re.M)
 for name in re.findall(r'^theorem (\w+)\b',text,re.M):roots.append(ns.group(1)+'.'+name)
roots=list(dict.fromkeys(roots));(E/'NHX_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[roots]),indent=2)+'\n')
catalog={x['module']:x for line in(B/'NHM_EXPECTED_IMPORTS.jsonl').read_text().splitlines()for x in[json.loads(line)]}
for name in mods+['NHX_COMBINED_IMPORT']:
 text=(E/(name+'.lean')).read_text();imports=[n for line in text.splitlines()if line.startswith('import ')for n in line[7:].split()if n!='all']
 # Lean implicitly imports Init in modules without prelude; canonical stable dedup.
 if not re.search(r'^prelude\b',text,re.M):imports=['Init']+imports
 catalog[name]=dict(module=name,imports=list(dict.fromkeys(imports)))
(E/'NHX_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(catalog[k])+'\n'for k in sorted(catalog)))
print(json.dumps(dict(owned_modules=len(mods),raw_roots=len(roots))))
