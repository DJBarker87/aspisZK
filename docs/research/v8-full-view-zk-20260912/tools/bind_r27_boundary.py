#!/usr/bin/env python3
"""Pin inspected source equations; not a Rust-to-Lean refinement checker."""
import argparse,hashlib,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--stage',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((a.stage/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(a.stage/n)==h,n
ex='docs/research/v8-no-work-100-20260907/experiments/'
requirements={
 'crates/aspis-core/src/sumcheck.rs':['let dual = [weights[0], weights[3], weights[2], weights[1]];','value.mul(*weight).mul_m31(M31_QUARTER)','polynomial[0]\n        .add(polynomial[4])'],
 'crates/aspis-core/src/field.rs':['pub const M31_QUARTER: M31 = M31(0x2000_0000);'],
 'crates/aspis-core/src/transcript.rs':['pub fn challenge_qm31(', 'let masked = word & crate::field::P;', 'if masked != crate::field::P {'],
 ex+'r17_host_relation.rs':['pub(super) fn channel_challenge(', 'let beta=sample(&mut p.t,false)?;'],
 ex+'relation_callback.rs':['fn sample(t:&mut Transcript,nonzero:bool)', 'if nonzero {t.challenge_nonzero_qm31()}else{t.challenge_qm31()}'],
 ex+'r17_c1_witness_audit.rs':['vec![vec![K::ZERO;1022];626]','assert_eq!(dot(rq,&wr),K::ZERO','matrix[625][j]=dot(&dw,&q);','[0,1,2,3,5,6]','target[625]=dot(&dw,rq).mul(scale.inv());','assert_eq!(scale.mul(dot(&dw,&q)),dot(&dw,rq)','for i in 0..7{assert_eq!(rp[i].add(scale.mul(gp[i])),K::ZERO);'],
 ex+'r17_coupled_audit.rs':['q.extend([abc[1].mul(x[1021]), abc[2].mul(x[1021]), K::ZERO]);'],
 ex+'r17_opening_weights.rs':['let scales = [kappa, kappa.square(), kappa.square().mul(kappa)];','if structured { out[j] = out[j].add(kappa.mul(scratch[j])); }','w[1023] = w[1023].add(t);','w[1022] = w[1022].add(tt.mul(abc[1]));','w[1021] = w[1021].sub(tt.mul(abc[2]));'],
}
files={}
for n,needles in requirements.items():
    path=a.stage/n;text=path.read_text()
    for needle in needles:assert needle in text,(n,needle)
    files[n]={'sha256':sha(path),'in_full_source_manifest':n in m['files'],'matched_equations':needles}
assert not a.output.exists();a.output.parent.mkdir(parents=True,exist_ok=True)
a.output.write_text(json.dumps({'source_manifest_sha256':sha(a.stage/'r18-stage.json'),'files':files,'beta_nonzero_assumed':False,'source_semantic_refinement_proved':False,'joint_image_existence_proved':False,'scope':'exact inspected equation inventory; conditional arithmetic bridge only'},indent=2)+'\n')
print(json.dumps({'status':'PASS','source_files':len(files),'all_manifest_pinned':all(x['in_full_source_manifest']for x in files.values()),'privacy_completion':False}))
