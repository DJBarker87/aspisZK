from pathlib import Path
import json,re
P=Path(__file__).resolve().parent;R=P.parents[1]
ns=json.loads((P/'JGy_NAMESPACE_MAP.json').read_text());inv={v:k for k,v in ns.items()}
pat=re.compile(r'\b('+'|'.join(sorted(map(re.escape,inv),key=len,reverse=True))+r')\b')
light=json.loads((P/'JGy_LIGHT.json').read_text());rows=[]
for row in json.loads((P/'JGy_CONSUMERS.json').read_text()):
 f=R/'lean'/f"{row['module']}.lean"
 actual='\n'.join(l for l in f.read_text().splitlines() if not l.startswith('import '))+'\n'
 actual=pat.sub(lambda m:inv[m[0]],actual)
 expected='\n'.join('\n'.join(l for l in (R/'lean'/f"{x['module']}.lean").read_text().splitlines() if not l.startswith('import '))+'\n' for x in row['originals'])
 for name in light['removed_unused_irreducible_attributes']:expected=expected.replace(' '+name,'')
 assert actual==expected,row['module']
 rows.append(dict(module=row['module'],all_declaration_types_and_proofs_preserved_after_namespace_substitution=True,removed_unused_attributes=light['removed_unused_irreducible_attributes'],originals=row['originals']))
(P/'JGy_CONSUMER_EQUIVALENCE.json').write_text(json.dumps(rows,indent=2)+'\n')
print('PASS:',len(rows),'consumer modules preserve inherited declarations')
