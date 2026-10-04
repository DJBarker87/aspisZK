use aspis_core as corelib;
use aspis_core::field::{CM31, M31, QM31 as K, M31_HALF, M31_QUARTER, P};
use aspis_core::sumcheck::{polynomial_for_extension, WeightAccumulator};

#[path = "/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a/docs/research/v8-no-work-100-20260907/experiments/r16_basis_transport.rs"]
mod basis_transport;
fn scalar(n: u32) -> K { K::from_cm31(CM31::from_m31(M31(n))) }

fn pow_small(x: K, n: usize) -> K {
    (0..n).fold(K::ONE, |a, _| a.mul(x))
}

fn dot(a: &[K], b: &[K]) -> K {
    a.iter().zip(b).fold(K::ZERO, |s, (&x, &y)| s.add(x.mul(y)))
}

// Ordinary (structured=false) selected opening weights. This is the literal
// formula in r17_opening_weights.rs; only its private crate-level optimized
// tensor-prefix helper is replaced by the public WeightAccumulator path.
fn ordinary_relation_weights(z:&[K;10],kappa:K,abc:[K;3])->WeightAccumulator {
    let map=basis_transport::transport();
    let scales=[kappa,kappa.square(),kappa.square().mul(kappa)];
    let mut original=WeightAccumulator::empty(10);
    for (scale,point) in scales.into_iter().zip(corelib::v6_transcript::v6_statement_points(z)) {
        original.add_multilinear(scale,point.to_vec()).unwrap();
    }
    let mut source=(0..1024).map(|i| {
        let mut x=original.weight_at(i as u32);
        if map.inactive[i] { x=x.add(K::ONE); }
        x
    }).collect::<Vec<_>>();
    let dual=map.dual(&source);
    source.clear();
    let mut quotient=chord_transpose(&dual,abc);
    // Selected ordinary wrapper tail adds tau, tau^2*abc[1], and
    // -tau^2*abc[2] at indices 1023,1022,1021 respectively. The candidate
    // q vectors are zero there, so tau=0 is value-neutral for these columns.
    let tau=K::ZERO;
    quotient[1023]=quotient[1023].add(tau);
    quotient[1022]=quotient[1022].add(tau.square().mul(abc[1]));
    quotient[1021]=quotient[1021].sub(tau.square().mul(abc[2]));
    let mut out=WeightAccumulator::empty(10);
    out.add_dense(quotient).unwrap();
    out
}

fn xt_transpose(v:&[K],n:usize)->Vec<K> {
    (0..n).map(|j| {
        let (mut row,mut bit,mut scale,mut sum)=(j,0,M31::ONE,K::ZERO);
        while row&(1<<bit)!=0 {
            row^=1<<bit;
            scale=scale.mul(M31_HALF);
            sum=sum.add(v[row].mul_m31(scale));
            bit+=1;
        }
        sum.add(v[row|(1<<bit)].mul_m31(scale))
    }).collect()
}

// Exact ordinary source chord transpose copied from r17_opening_weights.rs.
fn chord_transpose(w:&[K],[a,b,c]:[K;3])->Vec<K> {
    assert_eq!(w.len(),1024);
    let mut w=w.to_vec(); w.resize(1028,K::ZERO);
    let wa:Vec<_>=w.chunks_exact(2).map(|v|v[0]).collect();
    let wb:Vec<_>=w.chunks_exact(2).map(|v|v[1]).collect();
    let xwa=xt_transpose(&wa,513); let xxwa=xt_transpose(&xwa,512); let xwb=xt_transpose(&wb,512);
    let mut out=vec![K::ZERO;1024];
    for j in 0..512 {
        out[2*j]=a.mul(wa[j]).add(b.mul(xwa[j])).add(c.mul(wb[j]));
        out[2*j+1]=c.mul(wa[j].sub(xxwa[j])).add(a.mul(wb[j])).add(b.mul(xwb[j]));
    }
    out
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
// The following assertion checks this against the selected R16 transport.
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
    let rel = ordinary_relation_weights(&z, kappa, abc);
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
    let rel=ordinary_relation_weights(&z,kappa,abc);
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

fn limbs(x: K) -> [u32; 4] { [x.c0.a.0, x.c0.b.0, x.c1.a.0, x.c1.b.0] }

fn row_labels(rows: &[usize]) -> Vec<String> {
    let mut labels: Vec<_> = rows.iter().map(|r| format!("active_chord_{r}")).collect();
    labels.extend(["point_0", "point_1", "point_2"].into_iter().map(str::to_string));
    labels.extend(["ordinary_relation_1", "ordinary_relation_2", "ordinary_relation_3",
        "ordinary_relation_5", "ordinary_relation_6"].into_iter().map(str::to_string));
    labels
}

fn write_matrix(path: &str, m: &[Vec<K>], labels: &[String], pairs: &[(usize, usize)]) {
    use std::io::Write;
    let mut f=std::fs::File::create(path).expect("create raw matrix");
    writeln!(f,"rows={} columns={}",m.len(),pairs.len()).unwrap();
    for (col,(d,s)) in pairs.iter().enumerate() { writeln!(f,"column\t{col}\t{d}\t{s}").unwrap(); }
    for (r,row) in m.iter().enumerate() {
        write!(f,"row\t{r}\t{}",labels[r]).unwrap();
        for value in row { let [a,b,c,d]=limbs(*value); write!(f,"\t{a},{b},{c},{d}").unwrap(); }
        writeln!(f).unwrap();
    }
}

fn pivots(m: &mut [Vec<K>]) -> (Vec<usize>, Vec<usize>, Vec<usize>, Vec<Vec<K>>) {
    let n=m.len(); let cols=m[0].len(); let mut rank=0; let mut ps=Vec::new();
    let mut pivot_rows=Vec::new();
    let mut row_perm: Vec<_>=(0..n).collect();
    let mut left=vec![vec![K::ZERO;n];n];
    for i in 0..n { left[i][i]=K::ONE; }
    for col in 0..cols {
        let Some(p)=(rank..n).find(|&r|m[r][col]!=K::ZERO) else { continue };
        m.swap(rank,p); left.swap(rank,p); row_perm.swap(rank,p);
        let inv=m[rank][col].inv();
        for x in &mut m[rank][col..] { *x=x.mul(inv); }
        for x in &mut left[rank] { *x=x.mul(inv); }
        let row=m[rank].clone();
        let left_row=left[rank].clone();
        for r in 0..n { if r!=rank {
            let f=m[r][col]; if f!=K::ZERO {
                for c in col..cols { m[r][c]=m[r][c].sub(f.mul(row[c])); }
                for c in 0..n { left[r][c]=left[r][c].sub(f.mul(left_row[c])); }
            }
        }}
        ps.push(col); pivot_rows.push(row_perm[rank]); rank+=1; if rank==n { break; }
    }
    let nullspace=left[rank..].to_vec();
    (ps,pivot_rows,row_perm,nullspace)
}

fn main() {
    let mode=std::env::args().nth(1).unwrap_or_else(||"generic".into());
    let vals=match mode.as_str() {
        "generic" => [2,3,4,5,6,7,8,9,10,11],
        // Shift the zero from z[5] to z[8]: the first block retains the
        // no-carry property while the exceptional source order 1009 receives
        // nonzero z[5] and z[8]=0.
        "shifted" | "shifted-matrix" => [1,1,2,3,4,2,2,3,0,2],
        _ => [1,1,2,3,4,0,2,3,4,2],
    };
    assert_eq!(M31_HALF.0,(P+1)/2);
    assert_eq!(M31_QUARTER.0,(P+1)/4);
    let z=vals.map(scalar);
    let (ok,fail,total)=low_constancy_check(z);
    println!("R724_LOW_CONSTANCY mode={mode} all_23x3={ok} differing_pairs={fail} tested_pairs={total}");
    let transport=basis_transport::transport();
    let order_mismatches=(0..1024).filter(|&j|transport.order[j]!=source_order(j)).count();
    println!("R724_ORDER_MAP transport_source_order_mismatches={order_mismatches} first_transport={:?} first_twoswap={:?}", &transport.order[..12], (0..12).map(source_order).collect::<Vec<_>>());
    if mode=="matrix" || mode=="shifted-matrix" {
        assert!(ok,"selected diagnostic witness did not satisfy checked low constancy");
        let (mut mat,pairs)=matrix(z);
        let rows=active_rows();
        let labels=row_labels(&rows);
        let evidence_dir=if mode=="shifted-matrix" { "attempt-c-shifted" } else { "attempt-c" };
        std::fs::create_dir_all(evidence_dir).expect("create matrix evidence directory");
        write_matrix(&format!("{evidence_dir}/matrix.raw.tsv"),&mat,&labels,&pairs);
        let (p,pivot_rows,row_perm,nullspace)=pivots(&mut mat);
        let extra:Vec<_>=p.iter().copied().filter(|&c|c>=214).collect();
        let null_limbs: Vec<_>=nullspace.iter().map(|r|r.iter().map(|x|limbs(*x)).collect::<Vec<_>>()).collect();
        println!("R724_MATRIX mode={mode} rows=222 columns={} rank={} pivot_columns={:?} pivot_source_rows={:?} reduced_row_to_source_row={:?} core_pivots={} extra_pivots={:?} core_pairs={:?} supplemental_pairs={:?} left_nullity={} left_nullspace_limbs={:?}",pairs.len(),p.len(),p,pivot_rows,row_perm,p.iter().filter(|&&c|c<214).count(),extra,&pairs[..214],&pairs[214..],nullspace.len(),null_limbs);
    }
}
