from pathlib import Path
import json,re
E=Path('evidence/pv-batch2-20261027')
rows=[]
for packet,suffix in [('extraction','001'),('extraction-weights','002')]:
 for op in (range(249,254) if suffix=='001' else range(251,254)):
  D=E/packet;R=D/f'aeneas-{op}-{suffix}';r=json.loads((R/'receipt.json').read_text());g=D/f'generated-{op}';f=g/'Funs.lean';text=f.read_text() if f.exists() else ''
  rows.append(dict(packet=packet,op=op,exit=r['exit'],root_emitted=bool(re.search(r'^def (?:host_sampler\.(?:gamma|ordinary)_sample|pv_b2_(?:new|raw|materialize))',text,re.M)),function_count=len(re.findall(r'^def ',text,re.M)),error=(R/'output.log').read_text()[:1800] if r['exit'] else None,receipt=str(R/'receipt.json')))
(E/'EXTRACTION.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps([{k:r[k] for k in ['packet','op','exit','root_emitted','function_count']} for r in rows],indent=2))
