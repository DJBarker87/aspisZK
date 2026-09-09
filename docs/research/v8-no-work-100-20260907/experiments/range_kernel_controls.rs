//! Focused scalar range-kernel controls. Synthetic values only.
extern crate alloc;
#[path="../../../../crates/aspis-core/src/field.rs"]
mod field;
use field::{M31,CM31,QM31,P};
fn r(x:u128)->u32{(x%u128::from(P)) as u32}
#[test]
fn scalar_and_tower_boundary_differentials(){
    let edge=[0,1,2,3,P/2,P/2+1,P-3,P-2,P-1];
    let check=|a:u32,b:u32|{
        let(x,y)=(M31(a),M31(b));
        assert_eq!(x.add(y).0,r(a as u128+b as u128));
        assert_eq!(x.sub(y).0,r(a as u128+P as u128-b as u128));
        assert_eq!(x.neg().0,r(P as u128-a as u128));
        assert_eq!(x.mul(y).0,r(a as u128*b as u128));
        assert_eq!(x.half().double(),x);
    };
    for a in edge{for b in edge{check(a,b);}}
    let mut state=0x6138627367616du64;
    let mut next=||{state=state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);(state%P as u64) as u32};
    for _ in 0..8192{
        let(a,b,c,d)=(next(),next(),next(),next());check(a,b);
        let(x,y)=(CM31::new(M31(a),M31(b)),CM31::new(M31(c),M31(d)));
        let expected=CM31::new(M31(r(a as u128*c as u128+(P as u128)*P as u128-b as u128*d as u128)),
          M31(r(a as u128*d as u128+b as u128*c as u128)));
        assert_eq!(x.mul(y),expected);
        assert_eq!(x.square(),x.mul(x));
        let q=QM31{c0:x,c1:y};assert_eq!(q.square(),q.mul(q));
        if q!=QM31::ZERO{assert_eq!(q.mul(q.inv()),QM31::ONE);}
    }
    for x in [0,1,P as u64,(P as u64)*4,u32::MAX as u64,(1u64<<63),u64::MAX-1,u64::MAX]{
        assert_eq!(M31::reduce_u64(x).0,r(x as u128));
    }
}
#[test]
fn independent_qm31_eight_limb_products(){
    let to_q=|v:[u32;4]|QM31{c0:CM31::new(M31(v[0]),M31(v[1])),c1:CM31::new(M31(v[2]),M31(v[3]))};
    let check=|aa:[u32;4],bb:[u32;4]| {
        let a=aa.map(u128::from);let b=bb.map(u128::from);let pad=8*u128::from(P).pow(2);
        let expected=to_q([
            r(pad+a[0]*b[0]+2*a[2]*b[2]-a[1]*b[1]-2*a[3]*b[3]-a[2]*b[3]-a[3]*b[2]),
            r(pad+a[0]*b[1]+a[1]*b[0]+a[2]*b[2]+2*a[2]*b[3]+2*a[3]*b[2]-a[3]*b[3]),
            r(pad+a[0]*b[2]+a[2]*b[0]-a[1]*b[3]-a[3]*b[1]),
            r(a[0]*b[3]+a[1]*b[2]+a[2]*b[1]+a[3]*b[0]),
        ]);
        let (x,y)=(to_q(aa),to_q(bb));
        assert_eq!(x.mul(y),expected);
        assert_eq!(field::PreparedQm31Multiplier::new(x).mul(y),expected);
    };
    for mask in 0..256{check(core::array::from_fn(|j|if mask&(1<<j)==0{0}else{P-1}),
        core::array::from_fn(|j|if mask&(1<<(j+4))==0{0}else{P-1}));}
    let mut state=0x5a1937u64;
    for _ in 0..8192{
        let mut next=||{state=state.wrapping_mul(6364136223846793005).wrapping_add(1);(state%u64::from(P)) as u32};
        check(core::array::from_fn(|_|next()),core::array::from_fn(|_|next()));
    }
}
