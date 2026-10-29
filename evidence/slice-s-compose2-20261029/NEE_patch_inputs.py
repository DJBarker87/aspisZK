"""Read immutable patch inputs; never commit a separate Rust harness source copy."""
from pathlib import Path
E=Path(__file__).resolve().parent
def oracle_parts():
    patch=(E/'NEE_K005-NEE_oracle.patch').read_text()
    first,hook=patch.split('--- a/',1)
    body='\n'.join(l[1:] for l in first.splitlines()[3:] if l.startswith('+'))+'\n'
    return body.split('#[kani::proof_for_contract(aspis_core::field::M31::to_le_bytes)]')[0], '--- a/'+hook
