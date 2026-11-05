from pathlib import Path
import json,hashlib,difflib,subprocess
B=Path(__file__).resolve().parent;S=B/'NIX_src';n='crates/aspis-core/src/circle.rs';p=S/n
frozen=p.read_text();assert 'mod NIX_circle' not in frozen
p.write_text(frozen+'\n'+(B/'NIX_circle.rs.txt').read_text())
x=json.loads((B/'NIX_SOURCE_PINS.json').read_text());x[n]=hashlib.sha256(p.read_bytes()).hexdigest();(B/'NIX_SOURCE_PINS.json').write_text(json.dumps(x))
x=json.loads((B/'NIX_FROZEN_FILE_PINS.json').read_text());del x[n];(B/'NIX_FROZEN_FILE_PINS.json').write_text(json.dumps(x))
(B/'NIX_CIRCLE.patch').write_text(''.join(difflib.unified_diff(frozen.splitlines(True),p.read_text().splitlines(True),fromfile='a/'+n,tofile='b/'+n)))
print('NIX circle local-record dispatch installed')
