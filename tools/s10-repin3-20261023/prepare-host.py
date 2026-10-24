#!/usr/bin/env python3
"""Private copies of immutable inputs required by the retained generators."""
import shutil
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-s10-repin3-20261023')
P=H.parent/'codex-cx-s10-inventory3-20261021'
shutil.copy2(P/'frontier-input.json',H/'frontier-input.json')
(H/'packet').mkdir(exist_ok=True)
# Retained algorithms use both packet/ and collected/ input spellings.
shutil.copy2(H/'collected/elf-graphs.json',H/'packet/elf-graphs.json')
