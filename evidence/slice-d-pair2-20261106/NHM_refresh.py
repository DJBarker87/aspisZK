from pathlib import Path
import json,re
E=Path(__file__).resolve().parent;B=E.parent/'slice-d-pair-20261106'
mods=sorted(p.stem for p in E.glob('NHM_*.lean')if p.stem not in ['NHM_COMBINED_IMPORT','NHM_Driver','NHM_ProofDriver','NHM_FINAL_STATEMENTS'])
s='import NGK_COMBINED_IMPORT\nimport NHI_COMBINED_IMPORT\n'+''.join('import '+m+'\n'for m in mods)+'set_option autoImplicit false\n#check AspisR1.RPx_Deployed.deployed\n#print axioms AspisR1.RPx_Deployed.deployed\n'
for root in ['NHM_HighDot.cohort','NHM_PartialDot.cohort','NHM_ByteProducts.cohort','NHM_GroupRoot.cohort','NHM_Filled64.cohort','NHM_FactoredPrefix.source','NHM_SharedPartials.cohort','NHM_SharedHigh.cohort','NHM_RegularKinds.cohort']:
 s+='#check '+root+'\n#print axioms '+root+'\n'
(E/'NHM_COMBINED_IMPORT.lean').write_text(s)
base=json.loads((B/'NHI_AUDIT_ROOTS.json').read_text());roots=[r for g in base['groups']for r in g]
for module in mods:
 text=(E/(module+'.lean')).read_text();ns=re.search(r'^namespace ([\w.]+)',text,re.M)
 for name in re.findall(r'^theorem (\w+)\b',text,re.M):roots.append(ns.group(1)+'.'+name)
roots=list(dict.fromkeys(roots));(E/'NHM_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[roots]),indent=2)+'\n')
catalog={x['module']:x for line in(B/'NHI_EXPECTED_IMPORTS.jsonl').read_text().splitlines()for x in[json.loads(line)]}
for name in mods+['NHM_COMBINED_IMPORT']:
 text=(E/(name+'.lean')).read_text();imports=[n for line in text.splitlines()if line.startswith('import ')for n in line[7:].split()if n!='all']
 # Lean implicitly imports Init in modules without prelude; canonical stable dedup.
 if not re.search(r'^prelude\b',text,re.M):imports=['Init']+imports
 catalog[name]=dict(module=name,imports=list(dict.fromkeys(imports)))
(E/'NHM_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(catalog[k])+'\n'for k in sorted(catalog)))
print(json.dumps(dict(owned_modules=len(mods),raw_roots=len(roots))))
