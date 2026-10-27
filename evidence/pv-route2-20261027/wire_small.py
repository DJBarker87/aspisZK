from pathlib import Path
import difflib,json
D=Path('evidence/pv-route2-20261027');rows=json.loads((D/'candidates.json').read_text())
def diff(path,old,new):return ''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
# Complete host-only helper sum wiring; all three native host caller sites.
body=(D/'probes/230.rs').read_text();body=body.replace('use aspis_core::field::{M31,CM31,QM31,WideExact,P};','use aspis_core::field::QM31;');patch=diff('crates/aspis-r1-cost-probe/src/prover_helper_sum.rs','',body)
p='crates/aspis-r1-cost-probe/src/lib.rs';old=Path(p).read_text();patch+=diff(p,old,old+'\n#[cfg(feature="prover")]\nmod prover_helper_sum;\n')
for p in ['crates/aspis-r1-cost-probe/src/host_semantic.rs','crates/aspis-r1-cost-probe/src/prover.rs','crates/aspis-r1-cost-probe/src/sim.rs']:
 old=Path(p).read_text();new=old.replace('aspis_statement::state_only_copy_helper_sum','crate::prover_helper_sum::state_only_copy_helper_sum')
 if p.endswith('host_semantic.rs'):
  new=new.replace('multilinear_evaluate_qm31,state_only_copy_helper_sum,','multilinear_evaluate_qm31,');new='use crate::prover_helper_sum::state_only_copy_helper_sum;\n'+new
 patch+=diff(p,old,new)
(D/'patches/230.patch').write_text(patch)
# Fully owned/index generic encoder leaf and copied private basis builder.
body='''use aspis_core::r0::{CodeField,Message,domain::Point};
fn values<E:CodeField,const N:usize>(x:E)->[E;N] {
    let mut out=[E::ONE;N];let mut width=1usize;let mut factor=x;
    while width<N {
        let limit=width.min(N-width);let mut j=0usize;
        while j<limit {out[width+j]=out[j].mul(factor);j+=1;}
        width*=2;let square=factor.mul(factor);factor=square.add(square).sub(E::ONE);
    }
    out
}
fn eval_pair<E:CodeField>(q:&Message<E>,x:E)->(E,E) {
    let basis=values::<E,512>(x);let mut p0=E::ZERO;let mut p1=E::ZERO;
    let mut i=0usize;
    while i<512 {let n=basis[i];p0=p0.add(q[2*i].mul(n));p1=p1.add(q[2*i+1].mul(n));i+=1;}
    (p0,p1)
}
pub fn eval_message<E:CodeField>(q:&Message<E>,z:Point<E>)->E {
    let (p0,p1)=eval_pair(q,z.x);p0.add(z.y.mul(p1))
}
''';(D/'probes/79.rs').write_text(body);patch=diff('crates/aspis-r1-cost-probe/src/prover_encoder.rs','',body)
p='crates/aspis-r1-cost-probe/src/lib.rs';old=Path(p).read_text();patch+=diff(p,old,old+'\n#[cfg(feature="prover")]\nmod prover_encoder;\n')
for p in ['crates/aspis-r1-cost-probe/src/host_semantic.rs','crates/aspis-r1-cost-probe/src/prover.rs','crates/aspis-r1-cost-probe/src/sim.rs']:
 old=Path(p).read_text();new=old
 if p.endswith('host_semantic.rs'):new=new.replace(',encoder::eval_message','');new='use crate::prover_encoder::eval_message;\n'+new
 elif p.endswith('prover.rs'):new=new.replace('r0::encoder::eval_message','crate::prover_encoder::eval_message')
 else:new=new.replace('encoder::eval_message,','');new='use crate::prover_encoder::eval_message;\n'+new
 patch+=diff(p,old,new)
(D/'patches/79.patch').write_text(patch)
for row in rows:
 op=row['op'];t=(D/'patches'/f'{op}.patch').read_text().splitlines();row.update(added=sum(x.startswith('+') and not x.startswith('+++') for x in t),removed=sum(x.startswith('-') and not x.startswith('---') for x in t))
 if op in [79,230]:row['wiring']='complete patch, unapplied';row['callers']=['host_semantic','prover','sim']
(D/'candidates.json').write_text(json.dumps(rows,indent=2)+'\n')
