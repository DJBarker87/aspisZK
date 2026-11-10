#!/bin/bash
# writes PCVU_SCOPES.json from the per-scope receipts (every attempt directory with receipt.json)
cd "$(dirname "$0")"
python3 -B - <<'EOF'
import json,glob,os
rows=[]
for d in sorted(glob.glob('PCVU_[EL][0-9][0-9][0-9]')):
    f=d+'/receipt.json'
    if not os.path.exists(f): continue
    r=json.load(open(f))
    rows.append(dict(attempt=r['attempt'],kind=r['kind'],module=r.get('module'),exit=r['exit_status'],wall_s=round(r['wall_seconds'],1),peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r['source_revision'],axioms=r.get('print_axioms') if r['kind']=='lean' else None))
json.dump(dict(schema='PCVU_SCOPES/1',scopes=rows),open('PCVU_SCOPES.json','w'),indent=1)
print(len(rows),'scopes')
EOF
rm -rf __pycache__
