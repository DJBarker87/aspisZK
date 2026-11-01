"""Read-only evidence export. Never exports private fixture keys/recovery files."""
from pathlib import Path
import json,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-c474-20261029';H='/home/dombarker/project-offloads/codex-pv-c474-20261029';HOST='dombarker@100.108.41.90'
files=['audit-result.json','diagnostics-result.json','force-capture-scan.json','client-resolved-features.json','probes-resolved-features.json','window-start.json','quiet-before-window.json']
for mode in ['default','devnet','pool']:
 for name in ['comparison.json','command.json']:files.append('elf-'+mode+'/'+name)
files+=['runtime-private-final/acceptance.json','runtime-private/acceptance.json']
for name in files:
 p=E/name;p.parent.mkdir(exist_ok=True,parents=True)
 r=subprocess.run(['ssh',HOST,'cat '+H+'/'+name],capture_output=True,check=True)
 p.write_bytes(r.stdout)
# Separate names repair the two backtrace snapshot basenames used by audit.py.
pins=json.loads((E/'audit-result.json').read_text())['source_pins'];correction=[]
for i,(source,pin) in enumerate(pins.items()):
 label='std-backtrace.rs.txt' if source.startswith('/home/dombarker/.rustup') else ('anyhow-backtrace.rs.txt' if '/anyhow-' in source else Path(source).name+'.txt')
 r=subprocess.run(['ssh',HOST,'cat '+source],capture_output=True,check=True)
 import hashlib
 assert hashlib.sha256(r.stdout).hexdigest()==pin['sha256'],source
 (E/label).write_bytes(r.stdout);correction.append(dict(source=source,sha256=pin['sha256'],corrected_snapshot=label,original_snapshot=pin['snapshot']))
(E/'snapshot-correction.json').write_text(json.dumps(dict(reason='The original audit snapshot basename collided for std and anyhow backtrace.rs; both exact source hashes were recorded correctly. Separate read-only exports restore both artifacts without recompilation.',sources=correction),indent=2)+'\n')
