from pathlib import Path
import json,re
E=Path(__file__).resolve().parent;G=E.parent/'verify-observed-20261105'
modules=['NHG_Serializer','NHG_PublicTranscript','NHG_Lengths','NHG_CopyFrame','NHG_FieldSpec','NHG_Semantic','NHG_Begin13','NHG_Begin9','NHG_Begin5','NHG_Begin']
roots=['AspisR1.'+m+'.'+n for m in modules for n in re.findall(r'^theorem (\w+)',(E/(m+'.lean')).read_text(),re.M)]+['AspisR1.RPx_Deployed.deployed']
(E/'NHG_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[roots[i:i+12] for i in range(0,len(roots),12)]),indent=1))
(E/'NHG_COMBINED_IMPORT.lean').write_text('import NGK_COMBINED_IMPORT\nimport NGX_COMBINED_IMPORT\n'+''.join('import '+m+'\n' for m in modules)+''.join('#print axioms '+r+'\n' for r in roots))
lines=(G/'NGX_EXPECTED_IMPORTS.jsonl').read_text().splitlines();known={json.loads(l)['module']for l in lines}
for m in modules+['NHG_COMBINED_IMPORT']:
 assert m not in known
 lines.append(json.dumps(dict(module=m,imports=['Init']+re.findall(r'^import (\S+)',(E/(m+'.lean')).read_text(),re.M))))
(E/'NHG_EXPECTED_IMPORTS.jsonl').write_text('\n'.join(lines)+'\n')
print(len(roots),'audit roots')
