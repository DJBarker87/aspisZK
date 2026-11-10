#!/usr/bin/env python3
"""PCUH_gen_order.py: build PRVEq_r0_transport_order.lean: fresh PCQE_E001 Funs (renamed namespace, registration attributes stripped) + hand-written equalities against the compiled gate (RPz7_FIo_NativeFuns)."""
import re,sys
from pathlib import Path
sys.dont_write_bytecode=True
H=Path(__file__).resolve().parent
fresh=(H.parent/'prov-p1d-20261109/PCQE_E001_emitted/raw/PCQE_aspis_core_r0_transport/Funs.lean').read_text()
fresh=fresh.replace('import PCQE_aspis_core_r0_transport.Types\n','')
fresh=fresh.replace('PCQE_aspis_core_r0_transport','PRVFresh_PCQE_E001_order')
fresh=re.sub(r'(?m)^@\[rust_loop_body\]\n','',fresh)
fresh=re.sub(r'(?m)^@\[rust_loop\]\n','',fresh)
fresh=fresh.replace('import Aeneas\n','import Aeneas\nimport RPz7_FIo_NativeFuns\nimport PRVH_WrapAdd\n',1)
fresh=fresh.rstrip()+'\n\n'
proof=(H/'PCUH_order_proofs.lean.in').read_text()
(H/'PRVEq_r0_transport_order.lean').write_text(fresh+proof)
print('ok')
