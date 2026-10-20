#!/usr/bin/env python3
"""Pin unchanged source assignments from real producers to the Libra boundary."""
from pathlib import Path
import hashlib,json,subprocess,argparse
ap=argparse.ArgumentParser();ap.add_argument('--write',action='store_true');args=ap.parse_args()
tool=Path(__file__).resolve().parent;repo=tool.parents[4];area=tool.parents[1]
rev='39c2971dd16c95858a4cfd2c9ae35da052eacfa9';sha=lambda b:hashlib.sha256(b).hexdigest()
paths=['verifier.rs','weights.rs','r1_semantic.rs','r1_wire.rs','transport.rs']
sources={p:subprocess.check_output(['git','-C',str(repo),'show',rev+':crates/aspis-r1-cost-probe/src/'+p]) for p in paths}
v=sources['verifier.rs'];w=sources['weights.rs'];s=sources['r1_semantic.rs'];t=sources['transport.rs'];r=sources['r1_wire.rs']
checks={
 'alpha0_actual_scalar':b'let alpha0=t.scalar(29,v.round0,false);' in v,
 'alpha1_actual_scalar':b'([alpha0,t.scalar(30,&bytes,false)],31)' in v,
 'prepared_copies_semantic_alpha':b'semantic_alpha:sem.alpha' in v,
 'resume_strict_alpha':b'let gamma=r.e()?;let kappa=r.e()?;let alpha=[r.e()?,r.e()?];' in v,
 'resume_strict_semantic_alpha':b'for x in &mut semantic_alpha {*x=r.k()?;}' in v,
 'semantic_alpha_actual_call':b'alpha[round] = transcript.semantic_validated(prefix.validated_record(row)?)?;' in s,
 'semantic_validated_actual_sampler':b'Ok(qm31_sample(\n            &self.sample_block_validated(row, record.framed())?,\n        ))' in r,
 'weights_extra_exact_slots':b'.extra).write([alpha[8],alpha[9]])' in w,
 'caller_actual_alpha_slice':b'weights.pair(&p.alpha[..p.variant.folds()],v.final_message,p.kappa)?' in v,
 's2_two_folds':b'pub fn folds(self) -> usize { if self == Self::S1 { 1 } else { 2 } }' in t,
 'ap0_exact_powers4':b'let ap0=powers::<4>(alpha[0]);' in w,
 'ap1_two_fold_exact_powers4':b'let ap1=if folds==2 {powers::<4>(alpha[1])}else{[E::ONE;4]};' in w,
 's2_only_helper_substitution':b'let libra=if self.variant==Variant::S2 {factored_s2_libra_weights(&ap0,&ap1,self.extra)}else{twofold_libra_weights(&low,self.extra)};' in w,
}
assert all(checks.values()),[k for k,val in checks.items() if not val]
report=dict(revision=rev,sources={p:sha(b) for p,b in sources.items()},checks=checks,
 proof='CuSavingsLibraSourceOrigins.source_caller_context',
 logical_boundary='Actual producer execution witnesses, not arbitrary constructed Weights/Prepared records; fixed extraction/runtime boundaries retained. Source layout and assignment connection is an explicit inverse/source-inventory admission, not a newly emitted whole-transaction theorem.',
 unchanged_cryptographic_schedule=True)
target=area/'evidence/cu-equivalence-20261019/LIBRA-SOURCE-ORIGINS-AUDIT.json'
if args.write:target.write_text(json.dumps(report,indent=2)+'\n')
else:assert json.loads(target.read_text())==report
print(json.dumps(dict(actual_source_origins=len(checks),checks_passed=True,whole_transaction_reextraction=False)))
