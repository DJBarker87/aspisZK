//! Five fixed-width public dots; independent channels, shared weight preparation.
use super::*;
use corelib::field::QM31;
type Channels=[[M31;3];3];
fn parts(v:K)->Channels {
    let s=v.c0.add(v.c1);
    [[v.c0.a,v.c0.b,v.c0.a.add(v.c0.b)],
     [v.c1.a,v.c1.b,v.c1.a.add(v.c1.b)],
     [s.a,s.b,s.a.add(s.b)]]
}
fn inject(c:K)->[[u64;3];3] {
    let [a,b,d,e]=[c.c0.a,c.c0.b,c.c1.a,c.c1.b].map(|x|u64::from(x.0));
    let ad=a.wrapping_add(d);
    [[a,0,a.wrapping_add(b)],[0;3],[ad,0,ad.wrapping_add(b.wrapping_add(e))]]
}
// Literal selected reconstruction, whose range holds for arbitrary u64 channels.
#[inline]
fn reconstruct(sums:[[u64;3];3])->K{
        let f=|x:u64|(x&2147483647).wrapping_add(x>>31);
        let [[a,b,c],[d,e,fv],[g,h,i]]=sums.map(|row|row.map(f));
        let pad=68719476704u64;
        let r0=a.wrapping_add(d.wrapping_mul(3)).wrapping_add(pad)
            .wrapping_sub(b).wrapping_sub(e).wrapping_sub(fv);
        let r1=c.wrapping_add(fv.wrapping_mul(2)).wrapping_add(pad)
            .wrapping_sub(a).wrapping_sub(b).wrapping_sub(d).wrapping_sub(e.wrapping_mul(3));
        let r2=g.wrapping_add(b).wrapping_add(e).wrapping_add(pad)
            .wrapping_sub(h).wrapping_sub(a).wrapping_sub(d);
        let r3=i.wrapping_add(a).wrapping_add(b).wrapping_add(d).wrapping_add(e).wrapping_add(pad)
            .wrapping_sub(g).wrapping_sub(h).wrapping_sub(c).wrapping_sub(fv);
        return QM31{c0:CM31::new(M31::reduce_u64(r0),M31::reduce_u64(r1)),
            c1:CM31::new(M31::reduce_u64(r2),M31::reduce_u64(r3))};
}
/// Returns row[0] + sum(weights[j]*row[j+1]) for each independent row.
/// The caller passes gamma^1..gamma^28; gamma^0=1 is structural, not a guard.
#[inline(never)]
pub(super) fn five(weights:&[K;28],rows:[&[K;29];5])->[K;5] {
    let mut outer=rows.map(|r|inject(r[0]));
    for group in 0..7 {
        let left:[Channels;4]=core::array::from_fn(|j|parts(weights[4*group+j]));
        for row in 0..5 {
            let mut raw=[[0u64;3];3];
            for j in 0..4 {
                let right=parts(rows[row][1+4*group+j]);
                for i in 0..3 {for k in 0..3 {
                    raw[i][k]=raw[i][k].wrapping_add(u64::from(left[j][i][k].0).wrapping_mul(u64::from(right[i][k].0)));
                }}
            }
            for i in 0..3 {for k in 0..3 {
                let s=raw[i][k];let partial=(s&2147483647).wrapping_add(s>>31);
                outer[row][i][k]=outer[row][i][k].wrapping_add(partial);
            }}
        }
    }
    outer.map(reconstruct)
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn independent_five_rows_match() {
        let mut rng=0x6761_6d6d_6164_6f74u64;
        fn m(r:&mut u64)->M31{*r^=*r<<13;*r^=*r>>7;*r^=*r<<17;M31((*r%u64::from(corelib::field::P)) as u32)}
        fn k(r:&mut u64)->K{K{c0:CM31::new(m(r),m(r)),c1:CM31::new(m(r),m(r))}}
        let max=K{c0:CM31::new(M31(corelib::field::P-1),M31(corelib::field::P-1)),c1:CM31::new(M31(corelib::field::P-1),M31(corelib::field::P-1))};
        for case in 0..2048 {
            let mut weights=core::array::from_fn(|_|k(&mut rng));
            let mut rows:[[K;29];5]=core::array::from_fn(|_|core::array::from_fn(|_|k(&mut rng)));
            if case==0{weights=[K::ZERO;28];rows=[[K::ZERO;29];5];}
            if case==1{weights=[max;28];rows=[[max;29];5];}
            if case==2{weights=[K::ONE;28];}
            if (3..12).contains(&case){let g=if case==3{K::ZERO}else{k(&mut rng)};let mut p=K::ONE;
                for w in &mut weights{p=p.mul(g);*w=p;}}
            let out=five(&weights,rows.each_ref());
            let mut full=[K::ONE;29];full[1..].copy_from_slice(&weights);
            for r in 0..5 {
                assert_eq!(out[r],corelib::field::qm31_dot(&full,&rows[r]));
                assert_eq!(out[r],(0..28).fold(rows[r][0],|s,j|s.add(weights[j].mul(rows[r][j+1]))));
            }
        }
        for row in 0..5 {for index in 0..29 {for limb in 0..4 {
            let mut rows=[[K::ZERO;29];5];let mut v=[M31::ZERO;4];v[limb]=M31(corelib::field::P-1);
            rows[row][index]=K{c0:CM31::new(v[0],v[1]),c1:CM31::new(v[2],v[3])};
            let out=five(&[K::ONE;28],rows.each_ref());
            for r in 0..5{assert_eq!(out[r],if r==row{rows[row][index]}else{K::ZERO});}
        }}}
        println!("SHARED_GAMMA arbitrary_five_rows=2048 independent_basis=580 canonical_extremes=true gamma_zero_one=true");
    }
}
