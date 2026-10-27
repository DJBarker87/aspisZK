from pathlib import Path
import json,subprocess,shutil
E=Path('evidence/pv-integ1-20261027/d298');T=Path('tools/pv-integ3-20261027');H='dombarker@100.108.41.90';D='/home/dombarker/project-offloads/codex-pv-integ1-20261027/d298'
labels=json.loads((E/'elf-labels.json').read_text());all_labels=[*labels.values(),'build-pool-executable-wrapper','build-pool-executable-wrapper-reservation-02']
subprocess.run(['python3',str(T/'collect.py'),*all_labels],check=True)
summary={m:json.loads((E/label/'comparison.json').read_text()) for m,label in labels.items()};assert all(r['matches'] for r in summary.values())
(E/'elf-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
(E/'PROCESS.md').write_text('''D298 starts from 9ff5a4594e, with no implementation/proof source edits.
The prepared branch initially occupied pv-cb3; git worktree move placed it at
requested pv-cb without changing branch or HEAD. Existing host/evidence run
from 0c9dc9a4cc is preserved; D298 uses its own subdirectory.
Default/devnet succeeded directly. Pool: one aggregate reservation refusal,
three-minute cooldown, next fresh label admitted; compiler helper-thread
WouldBlock failure (1.029s,173256KiB,swap0) before project compilation. A changed
retry adds taskset --cpu-list 0-3 with unchanged -j4 and 6G/8G/swap0/Tasks64 caps.
Native compilation also receives this affinity proactively; runtime fixtures do not.
No failed build was rerun unchanged; no memory cap was raised.
Initial source upload preceded recording a separate upload reservation receipt;
build reservation and barrier both passed before any compilation. This ordering
missed local-lean rule7's pre-scp receipt requirement. Subsequent baseline and
runner uploads have dedicated admission receipts. No shared env-J source/object
was written. Scope execution is serial. SBF diagnostics include the same stack
warnings as predecessor builds; the byte-equal requested pins are the gate.
''')
for p in T.glob('__pycache__'):shutil.rmtree(p)
subprocess.run(['git','add','--',str(E),str(T)],check=True)
subprocess.run(['git','commit','-m','Record D298 verifier ELF integration pins','--',str(E),str(T)],check=True)
