from pathlib import Path
import json,re,difflib,hashlib,sys
E=Path(__file__).resolve().parent;P=E.parent/'q-field-rows-20261106';stage=sys.argv[1];assert stage in ['cm','final']
roots=['NHN_CMInstantiation.association','NHN_CMInstantiation.packet','NHN_CMInstantiation.outcomes']
mods=['NHN_CMInstantiation']
if stage=='final':
 mods+=['NHN_QNegAssociation'];roots+=['NHN_QNegAssociation.scalar','NHN_QNegAssociation.association','NHN_QNegAssociation.enclosing']
roots+=['AspisR1.RPx_Deployed.deployed']
(E/'NHN_COMBINED_IMPORT.lean').write_text('import NGK_COMBINED_IMPORT\nimport NHH_COMBINED_IMPORT\n'+''.join('import '+m+'\n'for m in mods)+'#print axioms AspisR1.RPx_Deployed.deployed\n')
s=(P/'NHH_Driver.lean').read_text();a=s.index('    else if mode == "scan"');b=s.index('\n    else ',s.index('else if mode == "proof11"'))
s=s[:a]+'''    else if mode == "scan" then (#[`NHN_COMBINED_IMPORT], #[])
    else if mode == "proof0" then
      (#[`NHN_COMBINED_IMPORT], #['''+', '.join('`'+r for r in roots)+'])'+s[b:]
s=s.replace('NHH_EXPECTED_IMPORTS','NHN_EXPECTED_IMPORTS').replace('NHH_LOADED_scan','NHN_LOADED_scan')
(E/'NHN_Driver.lean').write_text(s)
(E/('NHN_DRIVER_'+stage+'.diff')).write_text(''.join(difflib.unified_diff((P/'NHH_Driver.lean').read_text().splitlines(True),s.splitlines(True),fromfile='NHH_Driver.lean',tofile='NHN_Driver.lean')))
(E/'NHN_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots),indent=1)+'\n')
s=(P/'NHH_review_batch.py').read_text().replace('NHH_','NHN_');(E/'NHN_review_batch.py').write_text(s)
table=[json.loads(l)for l in (P/'NHH_EXPECTED_IMPORTS.jsonl').read_text().splitlines()]
for m in mods+['NHN_COMBINED_IMPORT']:
 src=(E/(m+'.lean')).read_text();table=[x for x in table if x['module']!=m];table.append(dict(module=m,imports=['Init']+[line[7:]for line in src.splitlines()if line.startswith('import ')]))
(E/'NHN_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(x)+'\n'for x in table))
# Walker and scanner are inherited unchanged; adapting root/module lists only.
(E/'NHN_WALKER_PIN.json').write_bytes((P/'NHH_WALKER_PIN.json').read_bytes())
