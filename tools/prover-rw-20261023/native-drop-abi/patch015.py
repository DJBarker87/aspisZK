"""Printer-only diagnostic candidate; nested Guard output is UNACCEPTED."""
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023')
p=H/'native-drop-abi/backend/base/src/PrePasses.ml'
p.write_bytes((H/'native-drop/backend/base/src/PrePasses.ml').read_bytes())
