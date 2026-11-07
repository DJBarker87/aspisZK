from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
rows=[]
for p in sorted(E.glob('LIB_L[0-9][0-9][0-9]/receipt.json')):
 x=json.loads(p.read_text());row={k:x[k]for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms']}
 source=E/(x['module']+'.lean')
 row['current_source']=source.exists() and hashlib.sha256(source.read_bytes()).hexdigest() in x['source_hashes'].values()
 row['canonical_revision2'] = int(x['attempt'][-3:]) >= 11 or x['module']=='LIB_Mark'
 row['accepted']=row['canonical_revision2'] and x['exit_status']==0 and row['current_source'] and all('sorryAx' not in a for a in x['print_axioms'])
 rows.append(row)
(E/'LIB_VALIDATION.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(dict(scopes=len(rows),current_passes=sum(r['accepted']for r in rows))))
