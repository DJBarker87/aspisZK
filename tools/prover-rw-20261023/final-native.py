#!/usr/bin/env python3
"""Frozen-source builds, relative gate, then the complete 1000-owner corpus."""
from pathlib import Path
import os,subprocess
R=Path(__file__).resolve().parents[2];H=R.parent;T=R/'tools/prover-rw-20261023'
# Build first. Timing has no simultaneous work from this orchestration.
subprocess.run(['python3',str(T/'native-gates.py'),'corpus-candidate-012','corpus'],check=True)
subprocess.run(['python3',str(T/'native-gates.py'),'pipeline-003','timing'],check=True)
subprocess.run(['python3',str(T/'run-host.py'),'interleaved-pipeline-003','python3',str(T/'interleaved.py'),'pipeline-003'],env=dict(os.environ,CT_EXPECTED='Five interleaved optimized v2/candidate complete proofs per fixture, 16 workers each; relative gate only'),check=True)
# Failure above is an explicit stop, not an invitation to launch later stages.
subprocess.run(['python3',str(T/'run-host.py'),'corpus-1000-002','python3',str(T/'corpus.py'),str(H/'native-artifacts/corpus-reference-009'),str(H/'native-artifacts/corpus-candidate-012'),str(H/'corpus-1000-002')],env=dict(os.environ,CT_EXPECTED='1000 optimized full retry-owner differential pairs; time in P_R1 elimination, 600 successful proof pairs and 100 forced-rejected-prefix pairs; 16 workers per process, two isolated processes'),check=True)
