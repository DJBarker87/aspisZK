from pathlib import Path
D=Path('evidence/pv-batch3-20261027');B=D/'bench3';B.mkdir(exist_ok=True)
s=(D/'bench2/Cargo.toml').read_text().replace('pv-b3-group2-bench','pv-b3-group3-bench').replace('group2-bench','group3-bench');(B/'Cargo.toml').write_text(s)
s=(D/'bench2/main.rs').read_text();s=s[:s.index('fn main(){')]
s+='''fn main(){
 use aspis_core::field::{M31,CM31,QM31};
 use aspis_core::state_only_prefix::r0::Challenges;
 use aspis_r1_cost_probe::host_public;
 assert!(!cfg!(debug_assertions));let lift=|n|QM31::from_cm31(CM31::from_m31(M31(n)));
 let c=Challenges{lambda:lift(17),chi:lift(23),theta:lift(29),zc:[lift(31);10],eta:lift(37),mu:lift(41)};
 let mut claims=[[QM31::ZERO;29];3];for p in 0..3{for l in 0..29{claims[p][l]=lift((p*29+l+2) as u32);}}
 for withdrawal in [false,true]{let fixture=aspis_prover::r0_fixture::prepare(withdrawal);let public=fixture.public();let tag=if withdrawal{"withdrawal"}else{"transfer"};
  assert_eq!(public.public_bytes(),host_public::materialize_public_bytes(public));
  bench(&format!("226-{tag}"),20,||public.public_bytes(),||host_public::materialize_public_bytes(public));
  for prefix in 0..11 {let mut point=[QM31::ZERO;10];for i in 0..prefix{point[i]=lift(17+i as u32);}for i in prefix..10{point[i]=if i%2==0{QM31::ZERO}else{QM31::ONE};}
   let old=||public.terminal_qm31(black_box(&claims),black_box(&point),black_box(&c));let new=||host_public::terminal_qm31(black_box(public),black_box(&claims),black_box(&point),black_box(&c));
   assert_eq!(old(),new());bench(&format!("227-{tag}-prefix-{prefix}"),10,old,new);
  }
 }
}
''';(B/'main.rs').write_text(s)
