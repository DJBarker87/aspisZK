#!/usr/bin/env python3
"""Read-only reachable hash-family inventory for the public proof-account route."""
from pathlib import Path
import hashlib,json,subprocess
E=Path(__file__).resolve().parent.parent
revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
rows=[
('public-statement','public-only','crates/aspis-r1-cost-probe/src/prover.rs',114,115,'H(public_bytes), public context and precommit binding; public nonce, tag, statement only'),
('reservation','public-only','crates/aspis-prover/src/state_only_entropy.rs',901,916,'SHA256(reservation domain || public nonce), no private seed; ledger path itself is not published'),
('attempt-binding','public-only','crates/aspis-prover/src/state_only_entropy.rs',862,875,'H(pool binding domain || precommit binding || context || fixed descriptor); PRIVATE in name does not make its bytes secret'),
('mask-seed','raw-field-suffix','crates/aspis-prover/src/state_only_hiding.rs',397,413,'H(mask seed domain || binding || context || field seed32)'),
('source-seed','raw-field-suffix','crates/aspis-prover/src/state_only_entropy.rs',426,432,'H(source seed domain || binding || context || same field seed32)'),
('leaf-salt','raw-leaf-suffix','crates/aspis-prover/src/state_only_entropy.rs',567,587,'H(leaf salt domain || public attempt binding || nonce || tree || index || leaf seed32); all three trees'),
('mask-blocks','private-derived','crates/aspis-prover/src/state_only_hiding.rs',1496,1499,'H(mask expand domain || derived mask seed32 || counter64)'),
('d-seed','private-derived','crates/aspis-prover/src/state_only_entropy.rs',647,654,'H(D domain || public attempt binding || derived source seed32)'),
('d-blocks','private-derived','crates/aspis-prover/src/state_only_entropy.rs',1256,1258,'H(profile21 expand domain || derived D seed32 || counter64)'),
('private-leaves','private-derived-and-semantic','crates/aspis-core/src/state_only_private_merkle.rs',29,50,'H(0x10 || tree || encoded masked values || derived salt32); caller C1/C2 and folded'),
('binary-nodes-roots','private-derived','crates/aspis-r1-cost-probe/src/multiproof.rs',48,80,'H(0x12 || left digest || right digest), including roots'),
('semantic-transcript','private-derived-and-semantic','crates/aspis-r1-cost-probe/src/r1_wire.rs',173,207,'Initial framing includes commitment root; semantic absorb/draw/update uses state and encoded messages'),
('tail-transcript','private-derived-and-semantic','crates/aspis-r1-cost-probe/src/transcript.rs',7,62,'Transcript new/absorb/draw/update and query scan blocks; seeded by semantic state'),
]
files={}
for role,kind,name,start,end,note in rows:
 p=Path(name);data=p.read_bytes();lines=data.decode().splitlines()
 files[name]=dict(sha256=hashlib.sha256(data).hexdigest(),size=len(data))
assertions=[]
for role,kind,name,start,end,note in rows:
 assertions.append(dict(role=role,classification=kind,file=name,line_start=start,line_end=end,note=note,excerpt='\n'.join(Path(name).read_text().splitlines()[start-1:end])))
for name in ['crates/aspis-r1-cost-probe/src/host_commitment.rs','crates/aspis-r1-cost-probe/src/host_semantic.rs','crates/aspis-prover/src/state_only_entropy.rs','crates/aspis-r1-cost-probe/src/sim.rs']:
 d=Path(name).read_bytes();files[name]=dict(sha256=hashlib.sha256(d).hexdigest(),size=len(d))
(E/'hash-input-inventory.json').write_text(json.dumps(dict(revision=revision,scope='generate_for_mask_nonce -> prove_masked_retrying_with, S2 with private-leaf-salts and r1p-check; reachable call-site families, not an executable source-refinement certificate',excluded='96-byte generate adapter; fixture APIs; legacy profile21/profile22/spend/other Pool variants; cfg(test) hooks; unselected unsalted leaf branch',files=files,families=assertions),indent=2)+'\n')
base=(E/'revision.txt').read_text().strip()
tracked=subprocess.check_output(['git','ls-tree','-r','--name-only',base,'--','crates','programs'],text=True).splitlines()
pins=[]
for name in tracked:
 data=Path(name).read_bytes();old=subprocess.check_output(['git','show',base+':'+name])
 assert data==old,name
 pins.append(dict(path=name,sha256=hashlib.sha256(data).hexdigest(),size=len(data)))
(E/'shipped-sources-unchanged.json').write_text(json.dumps(dict(base_revision=base,checked_revision=revision,all_equal=True,files=pins),indent=2)+'\n')
