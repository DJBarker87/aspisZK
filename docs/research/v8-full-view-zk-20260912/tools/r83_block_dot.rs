// Canonical closed-source ordinary contraction. Same powers, blocks, carry
// recurrence, final coefficients and scaling as block_terminal_scalar_impl.
#[inline(never)]
fn r83_block_terminal(w:&[[K;2];10],alpha:[K;4],[a,b,c]:[K;3],blocks:&[K],powers:&[(K,K);4],finals:&[K;4])->K {
    use corelib::field::{qm31_sum_products2 as dot2,qm31_sum_products3 as dot3,qm31_sum_products4 as dot4};
    let (a2,a3)=powers[0];let ax=alpha[0];
    let [x0,x1]=w[1];let [y0,y1]=w[0];
    let i0=x0.add(a2.mul(x1));let c0=a2.mul(x0).half();let s0=x1.add(c0);
    let i1=dot2([a3,ax],[x0,x1]);let c1=ax.mul(x0).half();let s1=a3.mul(x1).add(c1);
    let y0i1=y0.mul(i1);
    let u=dot3([a,b,c],[dot2([y0,y1],[i0,i1]),dot2([y0,y1],[s0,s1]),y1.mul(i0).add(y0i1.half())]);
    let v=dot2([b,c],[dot2([y0,y1],[c0,c1]),y0i1.half().neg()]);
    let mut identity=K::ONE;let mut ended=K::ZERO;let mut carry=K::ONE;
    for round in 1..4 {
        let z:&[K;4]=blocks[4*round..4*round+4].try_into().unwrap();
        let (a2,a3)=powers[round];let ax=alpha[round];
        let same=z[0].add(dot3([a3,a2,ax],[z[1],z[2],z[3]]));
        let stop=z[1].add(dot3([a3,a2,ax],[z[0].add(z[2]).half(),z[3],z[2].half().add(z[0].half().half())]));
        let next=ax.mul(z[0]).half().half();
        if round==1 {identity=same;ended=stop;carry=next;}
        else {identity=identity.mul(same);ended=dot2([ended,carry],[same,stop]);carry=carry.mul(next);}
    }
    let common=dot2([u,v],[identity,ended]);let active=v.mul(carry);
    let z:[K;4]=blocks[16..20].try_into().unwrap();
    let stop=[z[1],z[0].add(z[2]).half(),z[3],z[2].half().add(z[0].half().half())];
    let mut result=dot2([common,active],[dot4(z,*finals),dot4(stop,*finals)]);
    for _ in 0..8 {result=result.half();}result
}
