from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
rows=[json.loads(x.read_text()) for x in sorted(p.glob('NNR_L*/receipt.json'))]
cols=['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms']
(p/'NNR_COMPILE.tsv').write_text('\t'.join(cols)+'\n'+''.join('\t'.join(json.dumps(r[k]) if isinstance(r[k],(dict,list)) else str(r[k]) for k in cols)+'\n' for r in rows))
pins={str(x.relative_to(p)):dict(sha256=hashlib.sha256(x.read_bytes()).hexdigest(),bytes=x.stat().st_size) for x in p.glob('*.lean')}
(p/'NNR_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
print(json.dumps(dict(scopes=len(rows),passed=sum(r['exit_status']==0 for r in rows),failed=[r['attempt'] for r in rows if r['exit_status']!=0])))
