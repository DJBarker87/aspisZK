#!/usr/bin/env python3
"""Rebuild all three frozen verifiers from the host-only prover candidate."""
from pathlib import Path
import runpy,sys
R=Path(__file__).resolve().parents[2]
s=(R/'tools/ct-kernels-20261022/elf-host.py').read_text()
s=s.replace('40dc75742430dd198bd51d519aa5a41bad4a45e8f173ccbd51c6d5be344ac3f0','d7d42f770883401e0104fb6e044f61a132fea7359943db225d581c5740fcffd0').replace('12cb0bc2f8ff3993643638080a3786fdcd941910e5e4dd65ae2937a99290c28f','2b2a9f0e7a2f93004ddbf207d02f5c5d5155d5c9bfdaeed21a78d638ae9be922')
s=s.replace('tools/ct-kernels-20261022/run-host.py','tools/prover-rw-20261023/run-host.py')
# Execute the unchanged build mechanism with this stage's actual full pins.
exec(compile(s,str(__file__),'exec'))
