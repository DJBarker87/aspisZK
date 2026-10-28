from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
v=subprocess.check_output(['git','show',rev+':crates/aspis-r1-cost-probe/src/verifier.rs'],text=True)
c=subprocess.check_output(['git','show',rev+':crates/aspis-r1-cost-probe/src/candidate.rs'],text=True)
h=(E/'NBF_harness.rs.txt').read_text()
# Loop-body factoring changes only the owner/member names at its explicit cut.
row='''weights.push(j,a.power,basis_at(&basis,j));
        #[cfg(feature="prover")] {a.weights[j]=weights.value(j);}
        crate::trace::value(12,a.next*width+j,E::from_qm31(accumulated_weight_at(&a.weights,j)));
        crate::trace::value(13,a.next*width+j,E::from_m31(basis_at(&basis,j)));'''
assert row in v
factored='''weights.push(j,a.power,basis_at(basis,j));
 crate::trace::value(12,a.next*width+j,E::from_qm31(accumulated_weight_at(&a.weights,j)));
 crate::trace::value(13,a.next*width+j,E::from_m31(basis_at(basis,j)));'''
assert factored in h
assert 'basis[n+j]=basis[j].mul(node);' in v and 'basis[n+j]=basis[j].mul(node);' in h
assert 'raw[index]=[w.c0.a.0 as u64,w.c0.b.0 as u64,w.c1.a.0 as u64,w.c1.b.0 as u64];' in v and 'raw[index]=[w.c0.a.0 as u64,w.c0.b.0 as u64,w.c1.a.0 as u64,w.c1.b.0 as u64];' in h
tail='weights.terms+=1;\n    a.rhs=a.rhs.add(value.mul_qm31(a.power));crate::trace::value(11,a.next,a.rhs);\n    a.power=a.power.mul(p.rho);a.next+=1;'
assert tail in v
factored_tail='pending.terms+=1;\n a.rhs=a.rhs.add(value.mul_qm31(a.power));crate::trace::value(11,a.next,a.rhs);\n a.power=a.power.mul(rho);a.next+=1;'
assert factored_tail in h
out={'accumulation_tail_factoring':True,'tail_cut_parameters':'pending is reached weights; rho is reached p.rho','basis_iteration_factoring':True,'initialization_iteration_factoring':True,'frozen_revision':rev,'verifier_sha256':hashlib.sha256(v.encode()).hexdigest(),'candidate_sha256':hashlib.sha256(c.encode()).hexdigest(),'release_prover_feature':False,'row_loop_iteration_factoring':True,'row_factor_changes':['basis borrowed slice spelling','cfg(prover) branch absent in release'],'row_body_frozen_sha256':hashlib.sha256(row.encode()).hexdigest(),'row_body_factored_sha256':hashlib.sha256(factored.encode()).hexdigest(),'claims':'static source association only; native query high-level replacements remain open'}
(E/'NBF_ASSOCIATION.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
