#!/usr/bin/env python3
"""Direct-source CT codec and raw embedding contracts, no copied arithmetic."""
from pathlib import Path
import os,subprocess,sys
R=Path(__file__).resolve().parents[2]
names=sys.argv[1:] or ['exact_full_width_codec','raw_qm31_embedding_codec']
assert all(n in ['exact_full_width_codec','raw_qm31_embedding_codec','arbitrary_field_decoders_len16'] for n in names)
for name in names:
 cmd=['timeout','120','cargo','kani','--manifest-path','tools/prover-rw-20261023/contracts/Cargo.toml','--lib','--exact','--harness','field_codec_contracts::'+name,'--solver','kissat','--no-assertion-reach-checks','--output-format','terse','-j','1','-Z','unstable-options','--cbmc-args','--unwinding-assertions']
 subprocess.run(['python3',str(R/'tools/prover-rw-20261023/run-host.py'),'field-codec-kani-'+name,*cmd],env=dict(os.environ,CT_EXPECTED='Optimized Kani compilation then direct shipped CT canonical full-width codec or arbitrary raw QM31 embedding/codec check'),check=True)
