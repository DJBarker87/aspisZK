from pathlib import Path
import json,re,lzma,hashlib
E=Path(__file__).resolve().parent
stage1=E/'NGX_SCAN_STAGE1.jsonl.xz'
if not stage1.exists():
 raw=(E/'NGX_LOADED_scan.jsonl').read_bytes();stage1.write_bytes(lzma.compress(raw,preset=6));(E/'NGX_SCAN_STAGE1.jsonl.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
selected={'NGX_State':'NGX_L002','NGX_StateImpl':'NGX_L004','NGX_SemanticSample':'NGX_L015','NGX_SemanticDomain':'NGX_L016','NGX_SemanticNew':'NGX_L020','NGX_Payload':'NGX_L023','NGX_ParseRecord':'NGX_L029','NGX_SemanticRuntime':'NGX_L032','NGX_CodeTrace':'NGX_L038','NGX_SampleTrace':'NGX_L039','NGX_NewTrace':'NGX_L042','NGX_RecordAt':'NGX_L043'}
roots={'AspisR1.RPx_Deployed.deployed'}
for module,attempt in selected.items():
 r=json.loads((E/attempt/'receipt.json').read_text());assert r['exit_status']==0
 assert hashlib.sha256((E/(module+'.lean')).read_bytes()).hexdigest()==r['source_hashes']['NGX_generated/'+module+'.lean']
 roots.update(line.split("'")[1] for line in r['print_axioms'])
imports=['NGK_COMBINED_IMPORT']+list(selected)
(E/'NGX_COMBINED_IMPORT.lean').write_text(''.join('import '+m+'\n' for m in imports)+''.join('#print axioms '+n+'\n' for n in sorted(roots)))
base={r['module']:r['imports'] for r in map(json.loads,(E/'NGX_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
for module in selected|{'NGX_COMBINED_IMPORT':None}:
 base[module]=['Init']+re.findall(r'^import ([\w.]+)',(E/(module+'.lean')).read_text(),re.M)
(E/'NGX_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=n,imports=i))+'\n' for n,i in sorted(base.items())))
old=json.loads((E/'NGX_L009/sources/NGX_AUDIT_ROOTS.json').read_text())['groups'][0]
(E/'NGX_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[old,sorted(roots)]),indent=1))
(E/'NGX_STAGE2_TARGETS.json').write_text(json.dumps(selected,indent=1));print('roots',len(roots))
