"""Read-only source identity audit of this job's host copy; no build/monitoring."""
from pathlib import Path
import json,hashlib
b=Path(__file__).parent;x=json.loads((b/'PoolN_input-pins.json').read_text());rows=[]
for item in x['inputs']:
 p=item['path'];data=(b/'PoolN_src'/p).read_bytes();base=data[:item['bytes']];suffix=data[item['bytes']:]
 expected=b''.join((b/name).read_bytes() for name in x['suffixes'].get(p,[]))
 row={'file':p,'production_prefix_matches':hashlib.sha256(base).hexdigest()==item['sha256'],'suffix_matches':suffix==expected,'overlay_sha256':hashlib.sha256(data).hexdigest(),'suffix_sha256':hashlib.sha256(suffix).hexdigest(),'suffixes':x['suffixes'].get(p,[])};rows.append(row)
assert all(r['production_prefix_matches'] and r['suffix_matches'] for r in rows),[r for r in rows if not r['production_prefix_matches'] or not r['suffix_matches']]
print(json.dumps({'count':len(rows),'rows':rows,'scope':'Actual copied compiler inputs equal inherited frozen sources plus precisely named cfg(kani)-only suffixes; no ELF rebuild claimed'},indent=2))
