#!/usr/bin/env python3
"""Actual raw QM31 writer/canonicality-decoder frame on fixed 16-byte cells."""
from pathlib import Path
import os,subprocess
R=Path(__file__).resolve().parents[2]
cmd=['timeout','90','cargo','kani','--manifest-path','tools/prover-rw-20261023/contracts/Cargo.toml','--lib','--exact','--harness','raw_writer_contracts::raw_writer_and_decoder_frame','--solver','kissat','--no-assertion-reach-checks','--output-format','terse','-j','1','-Z','unstable-options','--cbmc-args','--unwinding-assertions']
subprocess.run(['python3',str(R/'tools/prover-rw-20261023/run-host.py'),'raw-writer-kani-001',*cmd],env=dict(os.environ,CT_EXPECTED='Optimized Kani compilation then all raw QM31 limbs, exact 16-byte writer/frame, and success iff canonical on re-decoding; no arithmetic aggregation'),check=True)
