"""Read immutable patch inputs; never commit a separate Rust harness source copy."""
from pathlib import Path
E=Path(__file__).resolve().parent
def oracle_parts():
    patch=(E/'NEE_K005-NEE_oracle.patch').read_text()
    first,hook=patch.split('--- a/',1)
    body='\n'.join(l[1:] for l in first.splitlines()[3:] if l.startswith('+'))+'\n'
    # Rule 16: keep only pure typed constructors. Historical oracle code is
    # preserved in per-attempt patches, never imported into a new harness.
    return body[:body.index('#[derive(Clone,Copy,Debug,PartialEq,Eq)]')], '--- a/'+hook
