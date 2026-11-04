"""Read only ELF mapping requests; never executes the adopted client."""
from pathlib import Path
import hashlib,json,subprocess
p=Path('/home/dombarker/project-offloads/codex-pv-c474-20261029/native-target/client/devnet_spend')
sha=lambda b:hashlib.sha256(b).hexdigest()
assert sha(p.read_bytes())=='da36d6aa36f8566ffa2ce7276546941c745bcd6325613c5a98c5517328b7def0'
tool=Path('/usr/bin/readelf')
print(json.dumps(dict(binary_sha256=sha(p.read_bytes()),executed=False,
 tool=dict(path=str(tool),sha256=sha(tool.read_bytes()),version=subprocess.check_output([str(tool),'--version'],text=True).splitlines()[0]),
 program_headers=subprocess.check_output([str(tool),'-lW',str(p)],text=True),
 elf_header=subprocess.check_output([str(tool),'-hW',str(p)],text=True),
 evidence_class='binary-structural (adopted binary), plus OS-model; V370 compiler-cohort')))
