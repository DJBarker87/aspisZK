#!/usr/bin/env python3
"""Pin the reached S2 source expressions, and cut the exact row30 append.
The inventory does not claim parser/extracted-caller refinement.
"""
from pathlib import Path
import json,hashlib,sys
R=Path(__file__).resolve().parents[2];C=R/'crates/aspis-r1-cost-probe/src'
E=R/'docs/research/100bit-spend-path-20261013/evidence/r4-transport2-20261021'
def compact(s):return ''.join(s.split())
v=(C/'verifier.rs').read_text();t=(C/'transcript.rs').read_text();s=(C/'r1_semantic.rs').read_text()
checks={
 'circle25':'let state_before_z0 = transcript.state();\nlet z0 = transcript.circle_validated(prefix.validated_record(25)?)?;',
 'circle26':'let before_z1 = prefix.validated_record(26)?.decode_k::<29>(0)?;\nlet z1 = transcript.circle_validated(prefix.validated_record(26)?)?;',
 'reseed':'let mut t=Transcript::new(hash,sem.transcript.state(),v.variant);',
 'row27':'let gamma=t.scalar(27,v.y1,true);',
 'row28':'let kappa=t.scalar(28,&v.inactive.to_le_bytes(),false);',
 'row29':'let alpha0=t.scalar(29,v.round0,false);',
 'row30':'let mut bytes=Vec::with_capacity(32+224);bytes.extend_from_slice(v.folded_root.unwrap());bytes.extend_from_slice(v.round1);',
 's2_rows':'([alpha0,t.scalar(30,&bytes,false)],31)',
 'row31_32':'let queries=t.queries(row,v.final_message)?;\nlet rho=t.scalar_k(row+1,&[]);',
 'absorb':'self.state=self.hash.digest(&[&self.state,&[0,0xa0+row],&(payload.len() as u32).to_le_bytes(),payload]);',
 'selected_return':'let (q,state)=aspis_core::r0_transcript::queries_from_pairs(&blocks,&advances).map_err(|_|crate::verifier::Error::Transcript)?;\nself.state=state;',
}
for name,body in checks.items():
 source=s if name.startswith('circle') else t if name in ['absorb','selected_return'] else v
 assert compact(body) in compact(source),name
# Check all sixteen actual eager reads and their adjacent carried-state links.
for k in range(8):
 for tag,arr in [(1,'blocks'),(2,'advances')]:
  assert compact(f'{arr}[{k}]=self.hash.digest(&[&state,&[{tag}]]);') in compact(t)
 assert compact(f'state=advances[{k}];') in compact(t)
result=dict(source_revision=__import__('subprocess').check_output(['git','rev-parse','HEAD'],text=True).strip(),sources={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [C/'verifier.rs',C/'transcript.rs',C/'r1_semantic.rs',C/'candidate.rs',C/'sampler.rs']},exact_fragments=checks,eager_pairs=8,scope='Source identity and reached call expressions only; binding these observations to the compiled caller, parsers and literal words is not inferred.')
(E/'prefix-source.json').write_text(json.dumps(result,indent=2)+'\n')
if len(sys.argv)>1:
 out=Path(sys.argv[1]);(out/'src').mkdir(parents=True,exist_ok=True)
 code='''#![allow(dead_code)]
struct View<'a>{folded_root:Option<&'a [u8;32]>,round1:&'a [u8]}
fn source_row30(v:&View)->Vec<u8>{'''+checks['row30']+''' bytes}
#[cfg(kani)] mod proofs {use super::*;
#[kani::proof] #[kani::unwind(258)] fn root_round1_bytes(){
let root:[u8;32]=kani::any();let round1:[u8;224]=kani::any();
let i:usize=kani::any();kani::assume(i<256);
let v=View{folded_root:Some(&root),round1:&round1};
let payload=source_row30(&v);
assert_eq!(payload.len(),256);
assert_eq!(payload[i],if i<32{root[i]}else{round1[i-32]});
}}
'''
 (out/'src/lib.rs').write_text(code)
 (out/'Cargo.toml').write_text('[package]\nname="r4-transport2-prefix"\nversion="0.0.0"\nedition="2021"\n[workspace]\n')
 (out/'source-cut.json').write_text(json.dumps(result,indent=2)+'\n')
