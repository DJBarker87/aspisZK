#!/usr/bin/env python3
"""Prepare, never apply, a minimal concrete tail-helper proposal."""
from pathlib import Path
import argparse,difflib,hashlib,json,subprocess
R=Path(__file__).resolve().parents[5];H=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
a=argparse.ArgumentParser();a.add_argument('--out',type=Path,required=True);a=a.parse_args()
pins=json.loads((H/'input/source-pins.json').read_text());file='crates/aspis-r1-cost-probe/src/verifier.rs';full=subprocess.check_output(['git','-C',str(R),'show',pins['revision']+':'+file],text=True);old=(H/'input/fragments/tx1.rs').read_text();assert full.count(old)==1
start=old.index('    let geometry=QueryGeometry::for_range(&p.queries,0,k)?;');end=old.rindex('\n}')
tail=old[start:end];assert tail.endswith('Ok(bytes)')
helper='''fn tx1_finish<H:Digest32>(v:View<'_>,p:Box<Prepared>,mut a:Accumulator,g:[E;29],public_bytes:&[u8],proof:&[u8],k:usize,hash:H,obs:Observer)->Result<Vec<u8>,Error> {
'''+tail+'\n}\n'
new=old[:start]+'    tx1_finish(v,p,a,g,public_bytes,proof,k,hash,obs)'+old[end:]
newfull=full.replace(old,helper+'\n'+new,1);a.out.mkdir(parents=True,exist_ok=True)
for n,b in {'tx1.rs':new.encode(),'tx1_finish.rs':helper.encode(),'verifier.rs':newfull.encode(),'proposal.patch':''.join(difflib.unified_diff(full.splitlines(True),newfull.splitlines(True),fromfile='a/'+file,tofile='b/'+file)).encode()}.items():(a.out/n).write_bytes(b)
audit={'classification':'REVIEW-ONLY PROPOSAL; no extraction probe, no production application','source_revision':pins['revision'],'source_file':file,'actual_tx1_sha256':sha(old.encode()),'proposed_tx1_sha256':sha(new.encode()),'helper_sha256':sha(helper.encode()),'moved_tail_sha256':sha(tail.encode()),'tail_correspondence':'Exact bytes: geometry setup, unchanged while, checkpoint, observer mark, Ok(bytes). All original owned locals transfer once to helper; helper is Result-returning and no operation, allocation, arithmetic or first-error order is added/reordered.','proposed_statement':helper.split('{\n',1)[0],'new_boundary':'verifier::tx1_finish','scope':'Allows visible actual tx1 prefix to be interpreted with a universal query/checkpoint continuation at a real source boundary; does not refine the opaque tail or current verify_observed source.','files':{p.name:sha(p.read_bytes()) for p in a.out.iterdir() if p.is_file() and p.name!='audit.json'}}
(a.out/'audit.json').write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n');print(json.dumps(audit,indent=2))
