"""Check every copied SHA fallback source byte modulo explicit namespace/literal ports."""
from pathlib import Path
import json,hashlib
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cblib-20261027';ref=(root/'tools/pv-cblib-20261027/lib.rs').read_text();src=(out/'source/sha2-0.10.9__src__sha256__soft.rs').read_text();const=(out/'source/sha2-0.10.9__src__consts.rs').read_text()
a=ref.index('pub mod sha_fallback_reference {\n')+len('pub mod sha_fallback_reference {\n');z=ref.index('\npub fn extracted_round(',a);body=ref[a:z];original=src[src.index('#[inline(always)]'):src.index('\npub fn compress(')]
assert body.replace('super::sha_fallback_consts::K32X4','crate::consts::K32X4').replace('($a >> 10u32)','($a >> 10)')==original
cb=const[const.index('pub const K32:'):const.index('/// Constants necessary for SHA-512')];assert cb in ref
r=dict(status='PASS',body_sha256=hashlib.sha256(body.encode()).hexdigest(),upstream_body_sha256=hashlib.sha256(original.encode()).hexdigest(),constant_sha256=hashlib.sha256(cb.encode()).hexdigest(),allowed_ports=['crate::consts::K32X4 namespace','10i32 inferred -> 10u32 explicit, literal count proofs 43018'],scope='Rust fallback only, not dispatcher or SHA-NI')
(out/'fallback-byte-check.json').write_text(json.dumps(r,indent=2)+'\n');print(r['status'])
