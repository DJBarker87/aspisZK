//! Structured chord transport: port of the previously tested product/grouped kernels.
//! No dense ordinary vector is constructed by this verifier path.
use super::*;

#[cfg(not(v8_performance_sbf))]
pub(in super::super) fn controls(){
    let sample=|n:u32|K{c0:CM31::new(M31(n+1),M31(n+3)),c1:CM31::new(M31(n+7),M31(n+11))};
    let mut entries=0;let mut terminals=0;
    for seed in 0..16u32{
        let z=core::array::from_fn(|j|if seed<3{[K::ZERO,K::ONE,K::ONE.neg()][seed as usize]}else{sample(seed*31+j as u32)});
        let scales=[sample(seed+2),sample(seed+3),sample(seed+4)];
        let abc=if seed==0{[K::ZERO;3]}else{[sample(seed+20),sample(seed+30),sample(seed+40)]};
        let d=Description::new(z,scales,abc);let original=materialize_original(&z,scales);
        #[cfg(v8_shared_weights)] for idx in [1,2]{let got=d.entry_pair(idx);assert_eq!(got,[original[0],original[idx]]);}
        for i in 0..1024{assert_eq!(d.entry(i),original[i]);entries+=1;}
        let alphas=if seed<4{[K::ZERO,K::ONE,K::ONE.neg(),K::ZERO]}else{core::array::from_fn(|j|sample(500+seed*4+j as u32))};
        let mut reference=WeightAccumulator::empty(10);reference.add_dense(transpose(&original,abc)).unwrap();
        for a in alphas{reference.fold_deferred_relation_arity4(a);}
        let terminal=d.terminal(alphas);
        for i in 0..4{assert_eq!(terminal[i],reference.weight_at(i as u32));terminals+=1;}
        // Interpolant can select either x (entry2) or y (entry1), including zero slope.
        for idx in [1,2]{for iv in [[K::ZERO,K::ZERO],[sample(seed+50),sample(seed+60)]]{
            assert_eq!(iv[0].mul(d.entry(0)).add(iv[1].mul(d.entry(idx))),iv[0].mul(original[0]).add(iv[1].mul(original[idx])));
        }}
    }
    for n in [1,4,22,44,88]{
        let v:Vec<K>=(0..n).map(|j|sample(j as u32)).collect();
        let inv=batch_inverse_k(&v).unwrap();assert_eq!(inv,tower_inverse_k(&v).unwrap());
        for j in 0..n{assert_eq!(inv[j],v[j].try_inv().unwrap());let mut bad=v.clone();bad[j]=K::ZERO;assert_eq!(batch_inverse_k(&bad),Err(Error::Domain));assert_eq!(tower_inverse_k(&bad),Err(Error::Domain));}
        let v:Vec<M31>=(0..n).map(|j|M31(1+j as u32)).collect();let inv=batch_inverse_m(&v).unwrap();
        for j in 0..n{assert_eq!(inv[j],v[j].inv());let mut bad=v.clone();bad[j]=M31::ZERO;assert_eq!(batch_inverse_m(&bad),Err(Error::Domain));}
    }
    let basis=[K::ONE,K::from_cm31(CM31::new(M31::ZERO,M31::ONE)),K{c0:CM31::ZERO,c1:CM31::ONE}];
    assert_eq!(tower_inverse_k(&basis).unwrap(),basis.iter().map(|v|v.inv()).collect::<Vec<_>>());
    #[cfg(v8_query_kernels)]
    for alpha in [K::ZERO,K::ONE,K::ONE.neg(),sample(777)]{
        for i in 0..256{let mut v=vec![K::ZERO;256];v[i]=sample(i as u32);assert_eq!(primal(&v,alpha),primal_reference(&v,alpha));}
    }
    println!("STRUCTURED_CONTROLS entries={entries} terminals={terminals} affine_x_y=true inversion_zero_every_position=true");
}


#[derive(Clone)]
pub(in super::super) struct Description {
    pub(in super::super) z:[K;10],pub(in super::super) scales:[K;3],pub(in super::super) abc:[K;3],
    #[cfg(v8_shared_weights)] points:Box<[[K;10];3]>,
    #[cfg(v8_reuse_gamma)] query_powers:Option<Box<StateOnlySpendQueryPowers>>,
}
impl Description {
    fn new(z:[K;10],scales:[K;3],abc:[K;3])->Self {
        Self{z,scales,abc,#[cfg(v8_shared_weights)] points:Box::new(corelib::v6_transcript::v6_statement_points(&z)),
            #[cfg(v8_reuse_gamma)] query_powers:None}
    }
    #[cfg(v8_shared_weights)]
    fn entry_pair(&self,index:usize)->[K;2]{
        assert!(index==1 || index==2);
        let groups=pool_v1_pair_forest_copy_inactive_row_groups_compiled_v1();
        let masks=pool_v1_pair_forest_copy_inactive_group_masks_compiled_v1();
        let mask=masks[groups[0] as usize];
        let mut out=[if mask&1!=0{K::ONE}else{K::ZERO},if mask&(1<<index)!=0{K::ONE}else{K::ZERO}];
        let target=if index==1{9}else{8};
        for(r,p)in self.points.iter().enumerate(){
            let mut common=self.scales[r];
            for j in 0..10{if j!=target{common=common.mul(K::ONE.sub(p[j]));}}
            let right=common.mul(p[target]);out[0]=out[0].add(common.sub(right));out[1]=out[1].add(right);
        }
        out
    }
    pub(in super::super) fn entry(&self,index:usize)->K {
        let groups=pool_v1_pair_forest_copy_inactive_row_groups_compiled_v1();
        let masks=pool_v1_pair_forest_copy_inactive_group_masks_compiled_v1();
        let mut out=if masks[groups[index/16] as usize]&(1<<(index%16))!=0{K::ONE}else{K::ZERO};
        #[cfg(not(v8_shared_weights))] let points=corelib::v6_transcript::v6_statement_points(&self.z);
        #[cfg(v8_shared_weights)] let points=*self.points;
        for (r,p) in points.into_iter().enumerate(){
            let value=p.iter().enumerate().fold(self.scales[r],|s,(j,x)|s.mul(if index&(1<<(9-j))==0{K::ONE.sub(*x)}else{*x}));
            out=out.add(value);
        }
        out
    }
    #[inline(never)]
    pub(in super::super) fn terminal(&self,alpha:[K;4])->[K;4] {
        let groups=pool_v1_pair_forest_copy_inactive_row_groups_compiled_v1();
        let masks=pool_v1_pair_forest_copy_inactive_group_masks_compiled_v1();
        let rows=core::array::from_fn(|i|masks[groups[i] as usize]);
        let mut out=grouped_terminal(&rows,self.abc,alpha).0;
        query_checkpoint("v8:grouped-terminal");
        #[cfg(not(v8_shared_weights))] let points=corelib::v6_transcript::v6_statement_points(&self.z);
        #[cfg(v8_shared_weights)] let points=*self.points;
        for (r,p) in points.into_iter().enumerate(){
            #[cfg(v8_fused_rows)] if r==2{continue;}
            let pairs=core::array::from_fn(|bit|[K::ONE.sub(p[9-bit]),p[9-bit]]);
            #[cfg(not(v8_fused_rows))]
            let value=block_terminal(&pairs,alpha,self.abc).0;
            #[cfg(v8_fused_rows)]
            let value=if r==0{
                let block: [K;4]=core::array::from_fn(|d|pairs[2][d&1].mul(pairs[3][d>>1]));
                let fused=core::array::from_fn(|d|self.scales[0].mul(block[d]).add(self.scales[2].mul(block[d^3])));
                block_terminal_impl(&pairs,alpha,self.abc,Some(fused)).0
            }else{block_terminal(&pairs,alpha,self.abc).0};
            #[cfg(not(v8_fused_rows))] let scale=self.scales[r];
            #[cfg(v8_fused_rows)] let scale=if r==0{K::ONE}else{self.scales[r]};
            for j in 0..4{
                #[cfg(all(v8_shared_weights,v8_fused_rows))]
                if r==0{out[j]=out[j].add(value[j]);continue;}
                out[j]=out[j].add(scale.mul(value[j]));
            }
        }
        out
    }
}
// Canonical verifier-derived description, never a prover-provided fingerprint.
// Prefix already binds statement/context ID, both commitments, semantic rounds,
// point claims, sequential OOD vectors, gamma, inactive claim and kappa.
// Explicit fixed framing below also binds ALL variable functional inputs and the
// actual expanded 64 binary row masks (128 bytes, not a claimed table digest).
#[inline(never)]
pub(in super::super) fn prepare(s:Semantic,w:&Wire<'_>)->Result<(Prefix,Description,K,K),Error>{
    let(mut t,points,gamma)=to_gamma(s.t,w)?;
    super::super::performance_verifier::checkpoint("v8:ood-gamma");
    t.absorb(label::V6_INACTIVE_CLAIM,&bytes(&w.v[358..359]));let kappa=sample(&mut t,true)?;
    let k2=kappa.square();let scales=[kappa,k2,k2.mul(kappa)];
    #[cfg(not(v8_shared_weights))]
    let batch=|v:&[K]|v.iter().rev().fold(K::ZERO,|a,v|a.mul(gamma).add(*v));
    #[cfg(v8_shared_weights)]
    let gp={let mut p=vec![K::ONE;29];for j in 1..29{p[j]=p[j-1].mul(gamma);}p};
    #[cfg(v8_shared_weights)]
    let batch=|v:&[K]|corelib::field::qm31_dot(&gp,v);
    let mut claim=w.v[358];for r in 0..3{claim=claim.add(scales[r].mul(batch(&w.v[271+29*r..300+29*r])));}
    let [s0,s1]=points;let use_x=s0.x!=s1.x;
    let h0=if use_x{s0.x}else{s0.y};let h1=if use_x{s1.x}else{s1.y};
    let y0=batch(&w.v[359..388]);let y1=batch(&w.v[388..417]);
    let slope=y0.sub(y1).mul(h0.sub(h1).try_inv().ok_or(Error::Domain)?);
    let iv=[y0.sub(slope.mul(h0)),slope];
    let abc=[s0.x.mul(s1.y).sub(s0.y.mul(s1.x)),s0.y.sub(s1.y),s1.x.sub(s0.x)];
    let mut d=Description::new(s.z,scales,abc);
    #[cfg(v8_reuse_gamma)] {
        let table:&[K;29]=gp.as_slice().try_into().unwrap();
        let prepared=StateOnlySpendQueryPowers::from_full_table(table);
        #[cfg(not(v8_performance_sbf))]
        assert_eq!(prepared,StateOnlySpendQueryPowers::new(gamma));
        d.query_powers=Some(Box::new(prepared));
    }
    #[cfg(not(v8_shared_weights))] let pair=[d.entry(0),d.entry(if use_x{2}else{1})];
    #[cfg(v8_shared_weights)] let pair=d.entry_pair(if use_x{2}else{1});
    claim=claim.sub(iv[0].mul(pair[0])).sub(iv[1].mul(pair[1]));
    let mut desc=b"AV8/functional/three-MLE-grouped64/chord/v2".to_vec();
    desc.extend([20,22,10,4,4,use_x as u8]);
    desc.extend(bytes(&d.z));desc.extend(bytes(&scales));desc.extend(bytes(&abc));desc.extend(bytes(&iv));
    desc.extend(bytes(&[s0.x,s0.y,s1.x,s1.y,gamma]));
    let groups=pool_v1_pair_forest_copy_inactive_row_groups_compiled_v1();
    let masks=pool_v1_pair_forest_copy_inactive_group_masks_compiled_v1();
    for j in 0..64{desc.extend(masks[groups[j] as usize].to_le_bytes());}
    t.absorb(label::PROFILE,&desc);t.absorb(label::CLAIM,&bytes(&[claim]));
    t.absorb(label::PROFILE,b"aspis-v8-image-gate-compact-functional-v2");
    let tau=sample(&mut t,true)?;
    Ok((Prefix{t,points,gamma,abc,iv,use_x,tau},d,claim,kappa))
}
#[inline(never)]
pub(in super::super) fn relation(w:&Wire<'_>,mut p:Prefix,d:Description,mut c:K)->Result<(),Error>{
    let mut a=[K::ZERO;4];
    let first=compact(&w.v[417..423],c);absorb_round(&mut p.t,0,&first);
    let mut work=vec![0];work.extend(&w.nonces[8..16]);p.t.absorb(label::M31_CIRCLE_FOLD_POW_NONCE,&work);
    a[0]=sample(&mut p.t,false)?;c=evaluate(&first,a[0]);
    let mut f=w.v[441..697].to_vec();let(q,rho)=query_schedule(&mut p,&f,w.nonces)?;
    super::super::performance_verifier::checkpoint("v8:query-schedule");
    #[cfg(not(v8_reuse_gamma))]
    let(values,xs)=opened_values(w,&p,&q,a[0],hash)?;
    #[cfg(v8_reuse_gamma)]
    let(values,xs)=opened_values_prepared(w,&p,&q,a[0],hash,d.query_powers.as_deref())?;
    // Only the fresh 256-dimensional line covectors are accumulated. They NEVER
    // pass through chord transpose or alpha0.
    let mut query_weights=WeightAccumulator::empty(8);
    let inc=inject(&mut query_weights,&mut c,&values,&xs,rho)?;
    p.t.absorb(label::PROFILE,&bytes(&[inc]));
    super::super::performance_verifier::checkpoint("v8:query-injection");
    for r in 1..4{
        let poly=compact(&w.v[417+r*6..423+r*6],c);absorb_round(&mut p.t,r,&poly);
        a[r]=sample(&mut p.t,false)?;c=evaluate(&poly,a[r]);
    }
    query_checkpoint("v8:relation-responses");
    // These public linear maps affect neither the scalar recurrence nor its
    // transcript. Defer them until all alphas are fixed, for disjoint profiling.
    for r in 1..4{query_weights.fold_deferred_relation_arity4(a[r]);}
    query_checkpoint("v8:query-weight-folds");
    for r in 1..4{f=primal(&f,a[r]);}
    query_checkpoint("v8:final-coefficient-folds");
    let terminal=d.terminal(a);
    super::super::performance_verifier::checkpoint("v8:structured-terminal");
    #[cfg(not(v8_performance_sbf))]
    {
        // Dense oracle under the SAME v2 transcript/challenges, all four entries.
        let mut reference=WeightAccumulator::empty(10);
        reference.add_dense(transpose(&materialize_original(&d.z,d.scales),d.abc)).unwrap();
        for alpha in a{reference.fold_deferred_relation_arity4(alpha);}
        for i in 0..4{assert_eq!(terminal[i],reference.weight_at(i as u32),"structured terminal differential");}
    }
    let expected=(0..4).fold(K::ZERO,|v,i|v.add(terminal[i].add(query_weights.weight_at(i as u32)).mul(f[i])))
        .add(image_terminal(p.tau,p.abc[1],p.abc[2],a).mul(f[3]));
    if expected==c{Ok(())}else{Err(Error::Terminal)}
}

// Direct two-bit contraction. Every m! is one counted generic QM31 product;
// half/add/sub and allocations are separate. Challenge squares are included.
fn block_terminal(w: &[[K; 2]; 10], alpha: [K; 4], [a, b, c]: [K; 3]) -> ([K; 4], usize) {
    block_terminal_impl(w,alpha,[a,b,c],None)
}
// A general four-entry replacement at bits 2/3. No rank-one factorisation,
// no live-factor inverses. This is the ONLY block changed by XOR12.
fn block_terminal_impl(w: &[[K; 2]; 10], alpha: [K; 4], [a,b,c]:[K;3],block1:Option<[K;4]>)->([K;4],usize){
    let mut count = 0usize;
    macro_rules! m {
        ($x:expr,$y:expr) => {{
            count += 1;
            ($x).mul($y)
        }};
    }
    let powers: [(K, K); 4] = core::array::from_fn(|j| {
        let a2 = m!(alpha[j], alpha[j]);
        (a2, m!(a2, alpha[j]))
    });
    let (a2, a3) = powers[0];
    let ax = alpha[0];
    let [x0, x1] = w[1];
    let [y0, y1] = w[0];
    let i0 = x0.add(m!(a2, x1));
    let c0 = m!(a2, x0).half();
    let s0 = x1.add(c0);
    let i1 = m!(a3, x0).add(m!(ax, x1));
    let c1 = m!(ax, x0).half();
    let s1 = m!(a3, x1).add(c1);
    let y0i1 = m!(y0, i1);
    let u = m!(a, m!(y0, i0).add(m!(y1, i1)))
        .add(m!(b, m!(y0, s0).add(m!(y1, s1))))
        .add(m!(c, m!(y1, i0).add(y0i1.half())));
    let v = m!(b, m!(y0, c0).add(m!(y1, c1))).sub(m!(c, y0i1).half());
    let mut identity = K::ONE;
    let mut ended = K::ZERO;
    let mut carry = K::ONE;
    for round in 1..4 {
        let k = 2 * round;
        let z = if round==1 && block1.is_some(){block1.unwrap()}else{[
            m!(w[k][0], w[k + 1][0]),
            m!(w[k][1], w[k + 1][0]),
            m!(w[k][0], w[k + 1][1]),
            m!(w[k][1], w[k + 1][1]),
        ]};
        let (a2, a3) = powers[round];
        let ax = alpha[round];
        let same = z[0].add(m!(a3, z[1])).add(m!(a2, z[2])).add(m!(ax, z[3]));
        let stop = z[1]
            .add(m!(a3, z[0].add(z[2])).half())
            .add(m!(a2, z[3]))
            .add(m!(ax, z[2].half().add(z[0].half().half())));
        let next = m!(ax, z[0]).half().half();
        identity = m!(identity, same);
        ended = m!(ended, same).add(m!(carry, stop));
        carry = m!(carry, next);
    }
    let common = m!(u, identity).add(m!(v, ended));
    let active = m!(v, carry);
    let z = [
        m!(w[8][0], w[9][0]),
        m!(w[8][1], w[9][0]),
        m!(w[8][0], w[9][1]),
        m!(w[8][1], w[9][1]),
    ];
    let stop = [
        z[1],
        z[0].add(z[2]).half(),
        z[3],
        z[2].half().add(z[0].half().half()),
    ];
    let out = core::array::from_fn(|j| {
        let mut r = m!(common, z[j]).add(m!(active, stop[j]));
        for _ in 0..8 {
            r = r.half();
        }
        r
    });
    (out, count)
}
fn basis(a: K, b: K) -> ([K; 16], usize) {
    let a2 = a.mul(a);
    let b2 = b.mul(b);
    let ap = [K::ONE, a2.mul(a), a2, a];
    let bp = [K::ONE, b2.mul(b), b2, b];
    let mut out = [K::ZERO; 16];
    let mut n = 4;
    for j in 0..16 {
        out[j] = if j < 4 {
            ap[j]
        } else if j % 4 == 0 {
            bp[j / 4]
        } else {
            n += 1;
            ap[j % 4].mul(bp[j / 4])
        };
    }
    (out, n)
}
#[inline(never)]
fn grouped_terminal(masks: &[u16; 64], [a, b, c]: [K; 3], alpha: [K; 4]) -> ([K; 4], usize, usize) {
    #[cfg(v8_grouped_linear)]
    let prepared_chord=[a,b,c].map(corelib::field::PreparedQm31Multiplier::new);
    let (low, mut products) = basis(alpha[0], alpha[1]);
    let (high, np) = basis(alpha[2], alpha[3]);
    products += np;
    let mut xn = [K::ZERO; 16];
    let mut xc = [K::ZERO; 16];
    let mut yn = [K::ZERO; 16];
    let mut yc = [K::ZERO; 16];
    // Forward local operators: an overflow is an ACTIVE carry into the high row,
    // not an ordinary integer increment of that row.
    for input in 0..16 {
        let y = input & 1;
        let j = input >> 1;
        for (r, s) in edges(j) {
            let dest = 2 * (r % 8) + y;
            if r < 8 {
                xn[dest] = xn[dest].add(low[input].mul_m31(s));
            } else {
                xc[dest] = xc[dest].add(low[input].mul_m31(s));
            }
        }
        if y == 0 {
            yn[input + 1] = yn[input + 1].add(low[input]);
        } else {
            yn[input - 1] = yn[input - 1].add(low[input].half());
            // y²=(1-T2)/2. Preserve bit zero of the line index.
            for (r, s) in edges(j >> 1) {
                let line = (r << 1) | (j & 1);
                let dest = 2 * (line % 8);
                let v = low[input].mul_m31(s).half();
                if line < 8 {
                    yn[dest] = yn[dest].sub(v);
                } else {
                    yc[dest] = yc[dest].sub(v);
                }
            }
        }
    }
    #[cfg(not(v8_grouped_linear))]
    let mut normal = [K::ZERO; 16];
    let mut carry = [K::ZERO; 16];
    #[cfg(not(v8_grouped_linear))]
    for j in 0..16 {
        normal[j] = a.mul(low[j]).add(b.mul(xn[j])).add(c.mul(yn[j]));
        products += 3;
    }
    // x's carry exits only at low positions 0/1; y's only at 0/2.
    // These follow from the largest line destinations 8 and 9 above.
    debug_assert!(xc[2..].iter().all(|v| *v == K::ZERO));
    debug_assert!(yc
        .iter()
        .enumerate()
        .all(|(j, v)| j == 0 || j == 2 || *v == K::ZERO));
    carry[0] = b.mul(xc[0]).add(c.mul(yc[0]));
    carry[1] = b.mul(xc[1]);
    carry[2] = c.mul(yc[2]);
    products += 4;
    let mut distinct = Vec::<u16>::new();
    let mut groups = [0usize; 64];
    for (j, mask) in masks.iter().enumerate() {
        groups[j] = match distinct.iter().position(|m| m == mask) {
            Some(i) => i,
            None => {
                distinct.push(*mask);
                distinct.len() - 1
            }
        };
    }
    let sums: Vec<(K, K)> = distinct
        .iter()
        .map(|mask| {
            #[cfg(not(v8_grouped_linear))]
            let mut n = K::ZERO;
            #[cfg(v8_grouped_linear)]
            let mut components = [K::ZERO;3];
            let mut c = K::ZERO;
            for j in 0..16 {
                if mask & (1 << j) != 0 {
                    #[cfg(not(v8_grouped_linear))]
                    { n = n.add(normal[j]); }
                    #[cfg(v8_grouped_linear)]
                    {
                        components[0]=components[0].add(low[j]);
                        components[1]=components[1].add(xn[j]);
                        components[2]=components[2].add(yn[j]);
                    }
                    c = c.add(carry[j]);
                }
            }
            #[cfg(v8_grouped_linear)]
            let n=corelib::field::qm31_sum_products3_prepared(&prepared_chord,&components);
            (n, c)
        })
        .collect();
    #[cfg(v8_grouped_linear)]
    { products+=3*distinct.len(); } // logical products; prepared kernel costs measured separately
    let mut out = [K::ZERO; 4];
    for j in 0..64 {
        let mut value = sums[groups[j]].0;
        for (r, s) in edges(j) {
            if r < 64 {
                value = value.add(sums[groups[r]].1.mul_m31(s));
            }
        }
        out[j >> 4] = out[j >> 4].add(value.mul(high[j & 15]));
        products += 1;
    }
    for value in &mut out {
        for _ in 0..8 {
            *value = value.half();
        }
    }
    (out, products, distinct.len())
}
