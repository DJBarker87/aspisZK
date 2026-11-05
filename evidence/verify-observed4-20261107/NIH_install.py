from pathlib import Path
import json,hashlib
B=Path(__file__).resolve().parent;S=B/'NIH_src'
p=S/'crates/aspis-statement/src/pool_v1/NHU_statement.rs';p.write_text((B/'NIH_statement.rs.txt').read_text())
prior=json.loads((B/('NIH_FROZEN_FILE_PINS.json' if (B/'NIH_FROZEN_FILE_PINS.json').exists() else 'NIH_prior_frozen.json')).read_text());pins=json.loads((B/('NIH_SOURCE_PINS.json' if (B/'NIH_SOURCE_PINS.json').exists() else 'NIH_prior_sources.json')).read_text())
pins['crates/aspis-statement/src/pool_v1/NHU_statement.rs']=hashlib.sha256(p.read_bytes()).hexdigest()
q='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs'
(S/q).write_text((B/'NIH_copy_terminal.rs.txt').read_text());prior.pop(q,None);pins[q]=hashlib.sha256((S/q).read_bytes()).hexdigest()
q='crates/aspis-statement/src/pool_v1/NIH_copy.rs'
(S/q).write_text((B/'NIH_copy.rs.txt').read_text());pins[q]=hashlib.sha256((S/q).read_bytes()).hexdigest()
for name,data in [('NIH_SOURCE_PINS.json',pins),('NIH_FROZEN_FILE_PINS.json',prior)]: (B/name).write_text(json.dumps(data,indent=2)+'\n')
print('installed split assertions without renaming')
