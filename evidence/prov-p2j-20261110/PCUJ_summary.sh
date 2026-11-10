#!/bin/bash
cd "$(dirname "$0")"
python3 -B - <<'PY'
import json,glob
rows=[]
for f in sorted(glob.glob('PCUJ_[EL][0-9][0-9][0-9]/receipt.json')):
    r=json.load(open(f))
    rows.append(dict(attempt=r['attempt'],kind=r['kind'],target=r['module'],exit=r['exit_status'],wall_s=round(r['wall_seconds'],1),peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r.get('source_revision'),axioms_lines=len(r['print_axioms']) if isinstance(r['print_axioms'],list) else None))
json.dump(dict(scopes=rows,lean_scopes=sum(1 for x in rows if x['kind']=='lean'),extraction_scopes=sum(1 for x in rows if x['kind']=='extract'),budget=dict(lean=45,extraction=20),caps=dict(lean='6G/8G swap 0 pids 64 timeout 180 unraised',extract='3G/4G swap 0 pids 64 timeout 180 unraised')),open('PCUJ_SCOPE_SUMMARY.json','w'),indent=1)
print(len(rows),max(float(x['peak_rss_kib']) for x in rows)/1048576,'GiB peak',max(x['wall_s'] for x in rows),'s max wall')
for x in rows: print(x['attempt'],x['exit'],x['wall_s'],x['target'])
PY
