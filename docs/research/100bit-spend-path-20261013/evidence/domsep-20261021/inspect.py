#!/usr/bin/env python3
"""Reproducible source pins and literal byte-format checks; no builds."""
import pathlib, subprocess, hashlib, json
root=pathlib.Path(__file__).resolve().parents[5]
ev=pathlib.Path(__file__).resolve().parent
paths=['crates/aspis-r1-cost-probe/src/'+p+'.rs' for p in ['candidate','multiproof','r1_wire','semantic_wire','transcript','verifier','r1_semantic','compact']]+['crates/aspis-core/src/merkle.rs','crates/aspis-core/src/r0/merkle.rs','crates/aspis-core/src/state_only_private_merkle.rs','crates/aspis-core/src/transcript.rs','crates/aspis-core/src/digest.rs','crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs','programs/r1-cost-probe/src/lib.rs']
sha=lambda b:hashlib.sha256(b).hexdigest()
pins=[]
for p in paths:
    frozen=subprocess.check_output(['git','show','b2727acd3:'+p],cwd=root)
    current=(root/p).read_bytes()
    pins.append(dict(path=p,frozen_sha256=sha(frozen),current_sha256=sha(current),frozen_bytes=len(frozen),current_bytes=len(current),identical=frozen==current))
domain=b'UNPROVED:R1:PRIVATE-SALTED:SEMANTIC:P3'
node=bytes([0x12])+bytes(32)+bytes([0xa1])+bytes(31)
endpoint=bytes([0x12])+bytes(31)
absorb=endpoint+bytes([0,0xa1])+bytes(31)
assert node==absorb and len(node)==65
assert len(domain)==38 and domain[0] not in [0x10,0x12]
# The row-one source record must be five zero bytes, rather than 31.
assert len(endpoint+bytes([0,0xa1])+bytes(5))==39
result=dict(frozen_revision=subprocess.check_output(['git','rev-parse','b2727acd3'],cwd=root,text=True).strip(),inspection_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),source_files=pins,checks=dict(domain_hex=domain.hex(),domain_bytes=len(domain),public_init_length='75 + public_bytes.length',binary_node_hex=node.hex(),ordinary_absorb_hex=absorb.hex(),equal=node==absorb,node_length=len(node),valid_source_row1_length=39,leaf_lengths={'C1':514,'C2':162,'folded':162}),claim='Byte-format inspection and literal equality checks; not Rust execution refinement, CU measurement, or an accepted-run counterexample.')
(ev/'source-pins.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'files':len(pins),'unchanged_since_frozen':sum(p['identical'] for p in pins),'literal_checks':'pass'},indent=2))
