use aspis_core as corelib;
use aspis_core::field::{CM31, M31, QM31 as K, M31_HALF, M31_QUARTER, P};
use aspis_core::sumcheck::{polynomial_for_extension, WeightAccumulator};

#[path = "/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a/docs/research/v8-no-work-100-20260907/experiments/r16_basis_transport.rs"]
mod basis_transport;
#[path = "/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a/docs/research/v8-no-work-100-20260907/experiments/r17_opening_weights.rs"]
mod opening_weights;

fn scalar(n: u32) -> K { K::from_cm31(CM31::from_m31(M31(n))) }

fn pow_small(x: K, n: usize) -> K {
    (0..n).fold(K::ONE, |a, _| a.mul(x))
}

fn dot(a: &[K], b: &[K]) -> K {
    a.iter().zip(b).fold(K::ZERO, |s, (&x, &y)| s.add(x.mul(y)))
}

// Exact source-shaped chord transform copied from r17_coupled_audit.rs.
fn xt(v: &[K]) -> Vec<K> {
    let mut out = vec![K::ZERO; v.len() + 1];
    for (j, &value) in v.iter().enumerate() {
        let (mut row, mut bit, mut scale) = (j, 0, M31::ONE);
        while row & (1 << bit) != 0 {
            row ^= 1 << bit;
            scale = scale.mul(M31_HALF);
            out[row] = out[row].add(value.mul_m31(scale));
            bit += 1;
        }
        out[row | (1 << bit)] = out[row | (1 << bit)].add(value.mul_m31(scale));
    }
    out
}

fn chord(q: &[K], [a, b, c]: [K; 3]) -> Vec<K> {
    let e: Vec<_> = q.chunks_exact(2).map(|v| v[0]).collect();
    let o: Vec<_> = q.chunks_exact(2).map(|v| v[1]).collect();
    let xe = xt(&e);
    let xo = xt(&o);
    let xxo = xt(&xo);
    let get = |v: &[K], i| v.get(i).copied().unwrap_or(K::ZERO);
    let mut out = vec![K::ZERO; 1028];
    for i in 0..514 {
        out[2 * i] = a.mul(get(&e, i))
            .add(b.mul(get(&xe, i)))
            .add(c.mul(get(&o, i).sub(get(&xxo, i))));
        out[2 * i + 1] = c.mul(get(&e, i))
            .add(a.mul(get(&o, i)))
            .add(b.mul(get(&xo, i)));
    }
    assert!(out[1024..].iter().all(|&v| v == K::ZERO));
    out.truncate(1024);
    out
}

fn pair(d: usize, s: usize, alpha: K) -> Vec<K> {
    let mut q = vec![K::ZERO; 1024];
    q[4*d+s] = K::ONE;
    q[4*d] = pow_small(alpha, s).neg();
    q
}

fn sub_assign(a: &mut [K], b: &[K]) {
    for (x, y) in a.iter_mut().zip(b) { *x = x.sub(*y); }
}

// TwoSwapSourceTable.order = swap(127,1023) then swap(126,1021) then base.
// This is intentionally distinct from the R16 transport permutation below.
fn source_order(j: usize) -> usize {
    let mut x=j;
    if x==127 { x=1023 } else if x==1023 { x=127 }
    if x==126 { x=1021 } else if x==1021 { x=126 }
    x%2+16*((x/2)%64)+2*(7-x/128)
}

fn active_rows() -> Vec<usize> {
    let map=basis_transport::transport();
    assert!((0..1024).all(|j|map.order[j]==source_order(j)),"R16 transport order differs from selected TwoSwapSourceTable.order");
    let inactive=&map.inactive;
    let mut high: Vec<_> = (0..1020).filter(|&j| !inactive[source_order(j)]).collect();
    assert_eq!(high.len(), 213);
    high.push(1022); // R707 rowCode for the extraTopColumn.
    assert_eq!(high.len(), 214);
    high
}

fn selected_core_pairs(rows: &[usize]) -> Vec<(usize, usize)> {
    let inactive=&basis_transport::transport().inactive;
    let block_active = |j: usize, s: usize| !inactive[source_order(4*(j/4)+s)];
    let mut out = Vec::new();
    for &j in &rows[..213] {
        let local = if j % 4 == 0 {
            if block_active(j, 1) {
                if block_active(j, 2) { 2 } else { 1 }
            } else { 0 }
        } else { j % 4 - 1 };
        let column = 3*(j/4-22)+local;
        let d=22+column/3; let s=1+column%3;
        assert!(d<255 && (1..4).contains(&s),"R698/R710 selected pair out of range");
        assert_eq!(3*(d-22)+(s-1),column,"R698 selected-column encode/decode");
        out.push((d,s));
    }
    // R698.extraTopColumn = 697, with R710's block/slot interpretation.
    out.push((22+697/3, 1+697%3));
    assert_eq!(out.len(), 214);
    let unique=out.iter().copied().collect::<std::collections::BTreeSet<_>>();
    assert_eq!(unique.len(),214,"R698 selected core pair collision");
    out
}

fn observations(
    q: &[K], rows: &[usize], points: &[Vec<K>], relation_weights: &WeightAccumulator,
) -> Vec<K> {
    assert!(q[1020..].iter().all(|&v|v==K::ZERO),"q tail 1020..1023 nonzero");
    let c = chord(q, [scalar(7), scalar(5), scalar(P-5)]);
    let m = basis_transport::transport().inverse(&c);
    assert_eq!(c[1023],K::ZERO,"sourceChord pivot tail");
    assert_eq!(m.iter().enumerate().filter(|(i,_)|basis_transport::transport().inactive[*i])
        .fold(K::ZERO,|s,(_,v)|s.add(*v)),K::ZERO,"actual inactive balance");
    assert_eq!(basis_transport::transport().forward(&m),c,"source R16 forward/inverse roundtrip");
    let mut out: Vec<_> = rows.iter().map(|&r| c[r]).collect();
    out.extend(points.iter().map(|w| dot(w, &m)));
    let poly = polynomial_for_extension(q, relation_weights);
    for k in [1usize, 2, 3, 5, 6] { out.push(poly[k]); }
    assert_eq!(out.len(), 222);
    out
}

fn fold_zero(q:&[K],alpha:K)->bool {
    (0..256).all(|d| {
        let mut acc=K::ZERO;
        for s in 0..4 { acc=acc.add(pow_small(alpha,s).mul(q[4*d+s])); }
        acc==K::ZERO
    })
}

fn low_constancy_check(z: [K; 10]) -> (bool, usize, usize) {
    let rows = active_rows();
    let alpha = scalar(7);
    let kappa = scalar(5);
    let abc = [scalar(7), scalar(5), scalar(P-5)];
    let rel = opening_weights::quotient_weights(&z, kappa, abc, K::ZERO, false);
    let points: Vec<Vec<K>> = corelib::v6_transcript::v6_statement_points(&z).iter().map(|p| {
        let mut w = WeightAccumulator::empty(10);
        w.add_multilinear(K::ONE, p.to_vec()).unwrap();
        (0..1024).map(|i| w.weight_at(i as u32)).collect()
    }).collect();
    let mut failures=0usize;
    let mut total=0usize;
    for d in 0..23 { for s in 1..4 {
        total+=1;
        let base = observations(&pair(0,s,alpha), &rows, &points, &rel);
        let obs=observations(&pair(d,s,alpha), &rows, &points, &rel);
        if obs!=base { failures+=1; }
    }}
    (failures==0,failures,total)
}

fn matrix(z: [K; 10]) -> (Vec<Vec<K>>, Vec<(usize,usize)>) {
    let rows=active_rows();
    let core=selected_core_pairs(&rows);
    let mut pairs=core.clone();
    for d in 23..32 { for s in 1..4 { pairs.push((d,s)); } }
    assert_eq!(pairs.len(),241);
    let alpha=scalar(7); let kappa=scalar(5);
    let abc=[scalar(7),scalar(5),scalar(P-5)];
    // tau affects only source tail terms 1021..1023; all candidate columns
    // vanish from index 1020 onward, so zero is a value-neutral placeholder.
    let rel=opening_weights::quotient_weights(&z,kappa,abc,K::ZERO,false);
    let points: Vec<Vec<K>> = corelib::v6_transcript::v6_statement_points(&z).iter().map(|p| {
        let mut w=WeightAccumulator::empty(10); w.add_multilinear(K::ONE,p.to_vec()).unwrap();
        (0..1024).map(|i|w.weight_at(i as u32)).collect()
    }).collect();
    let mut m=vec![vec![K::ZERO;pairs.len()];222];
    for (col,(d,s)) in pairs.iter().copied().enumerate() {
        let low=pair(0,s,alpha);
        let mut q=pair(d,s,alpha); sub_assign(&mut q,&low);
        assert!(fold_zero(&q,alpha),"first-fold polynomial does not vanish for column {col}");
        let v=observations(&q,&rows,&points,&rel);
        for r in 0..222 { m[r][col]=v[r]; }
    }
    (m,pairs)
}

fn pivots(m: &mut [Vec<K>]) -> Vec<usize> {
    let n=m.len(); let cols=m[0].len(); let mut rank=0; let mut ps=Vec::new();
    for col in 0..cols {
        let Some(p)=(rank..n).find(|&r|m[r][col]!=K::ZERO) else { continue };
        m.swap(rank,p);
        let inv=m[rank][col].inv();
        for x in &mut m[rank][col..] { *x=x.mul(inv); }
        let row=m[rank].clone();
        for r in 0..n { if r!=rank {
            let f=m[r][col]; if f!=K::ZERO {
                for c in col..cols { m[r][c]=m[r][c].sub(f.mul(row[c])); }
            }
        }}
        ps.push(col); rank+=1; if rank==n { break; }
    }
    ps
}

fn main() {
    let mode=std::env::args().nth(1).unwrap_or_else(||"generic".into());
    let vals=if mode=="generic" { [2,3,4,5,6,7,8,9,10,11] } else { [1,1,2,3,4,0,2,3,4,2] };
    assert_eq!(M31_HALF.0,(P+1)/2);
    assert_eq!(M31_QUARTER.0,(P+1)/4);
    let z=vals.map(scalar);
    let (ok,fail,total)=low_constancy_check(z);
    println!("R724_LOW_CONSTANCY mode={mode} all_23x3={ok} differing_pairs={fail} tested_pairs={total}");
    let transport=basis_transport::transport();
    let order_mismatches=(0..1024).filter(|&j|transport.order[j]!=source_order(j)).count();
    println!("R724_ORDER_MAP transport_source_order_mismatches={order_mismatches} first_transport={:?} first_twoswap={:?}", &transport.order[..12], (0..12).map(source_order).collect::<Vec<_>>());
    if mode=="matrix" {
        assert!(ok,"fixed certified witness did not satisfy checked low constancy");
        let (mut mat,pairs)=matrix(z);
        let p=pivots(&mut mat);
        let extra:Vec<_>=p.iter().copied().filter(|&c|c>=214).collect();
        println!("R724_MATRIX rows=222 columns=241 rank={} pivots={:?} core_pivots={} extra_pivots={:?} core_pairs={:?} supplemental_pairs={:?}",p.len(),p,p.iter().filter(|&&c|c<214).count(),extra,&pairs[..214],&pairs[214..]);
    }
}
