from pathlib import Path
import json,re
E=Path(__file__).resolve().parent;P=E.parent/'slice-d-pair3-20261106'
passed={}
for p in E.glob('NIG_L[0-9][0-9][0-9]/receipt.json'):
 r=json.loads(p.read_text())
 if r['exit_status']==0 and r.get('kind')=='lean':passed[r['module']]=r
mods=[]
for p in sorted(E.glob('NIG_*.lean')):
 if p.stem in ['NIG_Driver','NIG_ProofDriver','NIG_COMBINED_IMPORT','NIG_FINAL_STATEMENTS','NIG_ShiftInspect']:continue
 if p.stem not in passed:continue
 source=p.read_bytes();import hashlib
 receipt=passed[p.stem]
 key='NIG_generated/'+p.name
 assert receipt['source_hashes'][key]==hashlib.sha256(source).hexdigest(),p.name
 mods.append(p.stem)
(E/'NIG_COMBINED_IMPORT.lean').write_text('import NGK_COMBINED_IMPORT\nimport NHX_COMBINED_IMPORT\n'+''.join('import '+m+'\n'for m in mods)+'set_option autoImplicit false\n#check AspisR1.RPx_Deployed.deployed\n#print axioms AspisR1.RPx_Deployed.deployed\n')
base=json.loads((P/'NHX_AUDIT_ROOTS.json').read_text());roots=[v for g in base['groups']for v in g]
for m in mods:
 s=(E/(m+'.lean')).read_text();ns=re.search(r'^namespace ([\w.]+)',s,re.M)
 roots += [ns.group(1)+'.'+n for n in re.findall(r'^theorem (\w+)\b',s,re.M)]
roots=list(dict.fromkeys(roots));(E/'NIG_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[roots]),indent=2)+'\n')
catalog={x['module']:x for line in(P/'NHX_EXPECTED_IMPORTS.jsonl').read_text().splitlines()for x in[json.loads(line)]}
for m in mods+['NIG_COMBINED_IMPORT']:
 s=(E/(m+'.lean')).read_text();imports=['Init']+[n for l in s.splitlines()if l.startswith('import ')for n in l[7:].split()if n!='all']
 catalog[m]=dict(module=m,imports=list(dict.fromkeys(imports)))
(E/'NIG_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(catalog[k])+'\n'for k in sorted(catalog)))
(E/'NIG_QUALIFIED_MODULES.json').write_text(json.dumps(mods,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),roots=len(roots))))
