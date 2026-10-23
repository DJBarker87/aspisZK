#!/usr/bin/env python3
"""Full owned SDK candidate reborrows its already-owned public/proof buffers.
Preserve decode/validation/encoding/proof-acquire/error order and final release.
No production change or state/carrier erasure. Whole-parent equivalence required.
"""
from pathlib import Path
import sys,json,hashlib
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/modular-host/sources/owned-sdk-v3';O=Path(sys.argv[1]);(O/'src').mkdir(parents=True,exist_ok=True)
raw=(B/'src/lib.rs').read_text();s=raw
s=s.replace('pub fn owned_checkpoint_nonzero(bytes:Vec<u8>)->bool','pub fn owned_checkpoint_nonzero(bytes:&[u8])->bool')
s=s.replace('owned_checkpoint_nonzero(sdk.data_cells[checkpoint.data_slot].bytes.clone())','owned_checkpoint_nonzero(&sdk.data_cells[checkpoint.data_slot].bytes)')
a=' let public_data=sdk.data_cells[public.data_slot].bytes.clone();\n let statement=decode_public_statement_box(&public_data)?;'
b=' let statement={\n  let public_data=&sdk.data_cells[public.data_slot].bytes;\n  decode_public_statement_box(public_data)\n }?;'
assert s.count(a)==1;s=s.replace(a,b)
a=' let proof_data=sdk.data_cells[proof.data_slot].bytes.clone();'
b=' let public_data=&sdk.data_cells[public.data_slot].bytes;\n let proof_data=&sdk.data_cells[proof.data_slot].bytes;'
assert s.count(a)==1;s=s.replace(a,b)
(O/'src/lib.rs').write_text(s)
c=(B/'Cargo.toml').read_text().replace('name="aspis-s126-owned-sdk"','name="aspis-s126-owned-sdk-borrowed"');(O/'Cargo.toml').write_text(c)
sha=lambda x:hashlib.sha256(x.encode()).hexdigest()
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',freeze='b2727acd3abf79315d18b754a260f58f4b1c6326',source_sha256=sha(s),parent_source_sha256=sha(raw),qualification=__doc__,changes=['same full SDK/account/data/lamport/guard declarations and all fields','checkpoint scan borrows its owned bytes instead of cloning','decoder borrows public bytes in an explicit short scope before proof acquisition','after unchanged validation/encoding/proof acquisition, reborrow the same public Vec and proof Vec for the unchanged guards/first_decoded','same typed statement, error mapping, checkpoint update and reverse guard release'],remaining=['extract without borrow-elaboration failure','literal protocol/SDK/Ops identity and complete old/new owned parent equivalence, all statuses and states','native SDK/caller/child/scan/error/oracle-log transport; no adoption or re-pin implied']),indent=2)+'\n')
