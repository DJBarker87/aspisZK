from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent;R=D.parents[2]
for name,v in json.loads((D/'integration-inputs.json').read_text()).items():
 assert hashlib.sha256((R/name).read_bytes()).hexdigest()==v['after'],name
print('Scoped integration input hashes match.')
