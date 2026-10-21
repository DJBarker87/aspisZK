#!/usr/bin/env python3
"""Distinct fixed-word targets, serialised by the existing worker launcher."""
from pathlib import Path
import subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit13-20261021')
for i in range(8):
 name=f'source-word{i}-v2'
 print('Checking distinct target',name,flush=True)
 result=subprocess.run(['python3',str(H/'harness/kani.py'),name,f'state_only_entropy::scalar13::source_word_{i}'])
 if result.returncode:sys.exit(result.returncode)
