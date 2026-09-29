#!/usr/bin/env python3
"""Source-locked exact-output native experiments; never edit the control."""
import argparse, hashlib, json, shutil
from pathlib import Path
p=argparse.ArgumentParser()
p.add_argument('--control',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
p.add_argument('--variant',choices=['square','square-shortdot','semantic','powerbasis','shortinline','compose','privatebasis','scalarg'],required=True)
a=p.parse_args();src=a.control;dst=a.output;here=Path(__file__).parent
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='6a8d46585bcebaeca27fbb88c936e2379ce45f3f314a01f7d37d7b995bb8e8ab'
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==202
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not (dst/n).exists():
        (dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments'
ref=ex/'r81_reference';ref.mkdir();changed=[]
for n in ['field.rs','r23_width.rs','r24_guarded_qm.rs','r25_checked_dot.rs']:
    shutil.copy2(src/'crates/aspis-core/src'/n,ref/n);changed.append(ref/n)
field=dst/'crates/aspis-core/src/field.rs';s=field.read_text()
old='    pub fn square(self) -> QM31 {\n'
assert s.count(old)==1
s=s.replace(old,old+'        if let Some(result)=r24_canonical_mul(self,self) {return result;}\n')
if a.variant!='square':
    needle='fn qm31_sum_products_small<const N: usize>(left: [QM31; N], right: [QM31; N]) -> QM31 {\n'
    assert s.count(needle)==1
    s=s.replace(needle,needle+'    if let Some(out)=r81_short_dot(&left,&right,QM31::ZERO) {return out;}\n')
    for n in [2,3]:
        needle=f'pub fn qm31_sum_products{n}_prepared(left: &[PreparedQm31Multiplier; {n}], right: &[QM31; {n}]) -> QM31 {{\n'
        assert s.count(needle)==1
        extra=f'''    let raw:[QM31;{n}]=core::array::from_fn(|i| QM31 {{
        c0:CM31::new(left[i].components[0][0],left[i].components[0][1]),
        c1:CM31::new(left[i].components[1][0],left[i].components[1][1])}});
    if let Some(out)=r81_short_dot(&raw,right,QM31::ZERO) {{return out;}}
'''
        s=s.replace(needle,needle+extra)
    needle='''pub fn qm31_add_sum_products3_prepared(
    constant: QM31,
    left: &[PreparedQm31Multiplier; 3],
    right: &[QM31; 3],
) -> QM31 {
'''
    assert s.count(needle)==1
    extra='''    let raw:[QM31;3]=core::array::from_fn(|i| QM31 {
        c0:CM31::new(left[i].components[0][0],left[i].components[0][1]),
        c1:CM31::new(left[i].components[1][0],left[i].components[1][1])});
    if let Some(out)=r81_short_dot(&raw,right,constant) {return out;}
'''
    s=s.replace(needle,needle+extra)
    s+='\n'+(here/'r81_short_dot.rs').read_text()
    if a.variant in ['shortinline','compose','privatebasis','scalarg']:
        old='#[inline(never)]\nfn r81_short_dot'
        assert s.count(old)==1;s=s.replace(old,'#[inline(always)]\nfn r81_short_dot')
field.write_text(s);changed.append(field)
if a.variant in ['semantic','powerbasis','shortinline','compose','privatebasis','scalarg']:
    semantic=ex/'performance_verifier.rs';v=semantic.read_text()
    begin=v.index('        let mut poly=[K::ZERO;28];poly[0]=sent[0];')
    end=v.index('        let mut record=vec![r as u8];',begin)
    poly=v[begin:end]
    v=v[:begin]+v[end:]
    marker='''        if cache.is_empty() {
            #[cfg(not(v8_block_horner))]'''
    assert v.count(marker)==1
    v=v.replace(marker,'        if cache.is_empty() {\n'+poly+'            #[cfg(not(v8_block_horner))]')
    marker='''            #[cfg(not(target_os="solana"))]
            assert_eq!(s.claim,evaluate_state_only_polynomial(&poly,s.z[r]));'''
    assert v.count(marker)==1
    v=v.replace(marker,'''            #[cfg(not(target_os="solana"))] {
'''+poly+'''            assert_eq!(s.claim,evaluate_state_only_polynomial(&poly,s.z[r]));
            }''')
    # In the host reference check the old incoming claim must be retained.
    marker='''            s.claim=crate::r20_semantic_basis::evaluate_round(s.claim,sent.try_into().unwrap(),s.z[r],'''
    assert v.count(marker)==1
    v=v.replace(marker,'''            #[cfg(not(target_os="solana"))] let old_claim=s.claim;
'''+marker)
    refpoly=poly.replace('s.claim.sub','old_claim.sub').replace('missing(s.claim,','missing(old_claim,')
    v=v.replace('''            #[cfg(not(target_os="solana"))] {
'''+poly,'''            #[cfg(not(target_os="solana"))] {
'''+refpoly)
    semantic.write_text(v);changed.append(semantic)
if a.variant in ['powerbasis','compose','privatebasis','scalarg']:
    basis=ex/'r20_semantic_basis.rs'
    shutil.copy2(basis,ref/basis.name);changed.append(ref/basis.name)
    v=basis.read_text();needle='pub fn basis_into(x: K, out: &mut [K; ROUND_TERMS]) {\n'
    assert v.count(needle)==1
    v=v.replace(needle,needle+'''    if [x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0].iter().all(|&v|v<P) {
        // At degree d, out[d-1] is x^d. Only after every power is formed
        // do we subtract x. Even powers reuse the cheaper checked square.
        out[0]=x;
        for degree in 2..=27 {
            out[degree-1]=if degree%2==0 {out[degree/2-1].square()}
                else {out[degree-2].mul(x)};
        }
        for value in &mut out[1..] {*value=value.sub(x);}
        out[0]=K::ONE.sub(x.add(x));
        return;
    }
    // Preserve the old raw-constructor behavior outside the canonical case.
''')
    v+='\n'+(here/'r81_scale.rs').read_text()
    basis.write_text(v);changed.append(basis)
    semantic=ex/'performance_verifier.rs';v=semantic.read_text()
    old='''        let mut scale=M31::ONE;
        for r in (0..10).rev() {
            for v in &mut cache[1+27*r..1+27*(r+1)] {*v=v.mul_m31(scale);}
            scale=scale.mul(corelib::field::M31_HALF);
        }
        cache[0]=K::ONE.mul_m31(scale);'''
    new='''        for r in (0..10).rev() {
            for v in &mut cache[1+27*r..1+27*(r+1)] {
                *v=crate::r20_semantic_basis::scale_power_of_two(*v,9-r);
            }
        }
        cache[0]=crate::r20_semantic_basis::scale_power_of_two(K::ONE,10);'''
    assert v.count(old)==1;semantic.write_text(v.replace(old,new))
    test=ex/'r81_basis_check.rs';shutil.copy2(here/test.name,test);changed.append(test)
    if a.variant in ['privatebasis','scalarg']:
        canonical=ex/'r81_canonical_basis.rs'
        c=(ex/'r20_private_canonical.rs').read_text()
        begin=c.index('    #[inline(always)] pub fn mul(self,rhs:Self)->Self {')
        end=c.index('    pub(crate) fn from_reduced_limbs',begin)
        c=c[:begin]+'''    #[inline(always)] pub fn mul(self,rhs:Self)->Self {
        let [a,b,c,d]=self.0.map(u64::from);let [e,f,g,h]=rhs.0.map(u64::from);
        const PP:u64=(P as u64)*(P as u64);
        let partial=|x:u64|(x&u64::from(P)).wrapping_add(x>>31);
        let u=partial((c*g).wrapping_add(PP).wrapping_sub(d*h));
        let v=partial((c*h).wrapping_add(d*g));
        Self([reduce((a*e).wrapping_add(PP).wrapping_sub(b*f).wrapping_add(2*u).wrapping_add(3*u64::from(P)).wrapping_sub(v)),
            reduce((a*f).wrapping_add(b*e).wrapping_add(u).wrapping_add(2*v)),
            reduce((a*g).wrapping_add(c*e).wrapping_add(2*PP).wrapping_sub(b*h).wrapping_sub(d*f)),
            reduce((a*h).wrapping_add(b*g).wrapping_add(c*f).wrapping_add(d*e))])
    }
'''+c[end:]
        unchecked='''    pub(crate) fn from_reduced_limbs(x:[u32;4])->Self{
        debug_assert!(x.iter().all(|&a|a<P));Self(x)
    }
'''
        assert c.count(unchecked)==1;c=c.replace(unchecked,'')
        canonical.write_text(c);changed.append(canonical)
        v=basis.read_text()
        begin=v.index('    if [x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0].iter().all(')
        end=v.index('    // Preserve the old raw-constructor behavior',begin)
        v=v[:begin]+'''    if let Some(q)=r81_canonical::Q::from_limbs([x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]) {
        let mut powers=[r81_canonical::Q::ZERO;27];powers[0]=q;
        for degree in 2..=27 {
            powers[degree-1]=if degree%2==0 {let p=powers[degree/2-1];p.mul(p)}
                else {powers[degree-2].mul(q)};
        }
        powers[0]=r81_canonical::Q::ONE.sub(q.add(q));
        for i in 1..27 {powers[i]=powers[i].sub(q);}
        for i in 0..27 {
            let [a,b,c,d]=powers[i].limbs();
            out[i]=K{c0:aspis_core::field::CM31::new(M31(a),M31(b)),
                c1:aspis_core::field::CM31::new(M31(c),M31(d))};
        }
        return;
    }
'''+v[end:]
        v+='\n#[path="r81_canonical_basis.rs"] mod r81_canonical;\n'
        v+='\n'+(here/'r81_private_check.rs').read_text()
        basis.write_text(v)
        t=test.read_text();needle='    actual::differential_check('
        assert t.count(needle)==1
        test.write_text(t.replace(needle,'    actual::r81_private_kernel_check();\n'+needle))
if a.variant=='scalarg':
    scalar=ex/'r22_scalar.rs'
    scalar.write_text(scalar.read_text()+'\n'+(here/'r81_sparse_scalar.rs').read_text());changed.append(scalar)
    relation=ex/'r17_host_relation.rs';v=relation.read_text()
    old='''        let sparse=if let Some(coins)=coins {
            let (normal,carry,high)=kernel.geometry_parts();
            crate::r20_sparse_whole::sparse_terminal(coins,normal,carry,high,&mut workspace)
        }else{crate::r18_compact_g::terminal_shared(&z,&kernel,&mut workspace)};
        terminal=terminal.add(ordinary).add(corelib::field::qm31_sum_products4(
            sparse,core::array::from_fn(|i|finals[i])).mul(beta.mul(public_audit[10])));'''
    new='''        let sparse=if let Some(coins)=coins {
            let scalar=crate::r19_channel_ordinary::r81_sparse_scalar_after_ordinary(coins,&workspace,&kernel);
            #[cfg(not(target_os="solana"))] {
                let (normal,carry,high)=kernel.geometry_parts();
                let old=crate::r20_sparse_whole::sparse_terminal(coins,normal,carry,high,&mut workspace);
                assert_eq!(scalar,corelib::field::qm31_sum_products4(old,core::array::from_fn(|i|finals[i])));
            }
            scalar
        }else{corelib::field::qm31_sum_products4(
            crate::r18_compact_g::terminal_shared(&z,&kernel,&mut workspace),
            core::array::from_fn(|i|finals[i]))};
        terminal=terminal.add(ordinary).add(sparse.mul(beta.mul(public_audit[10])));'''
    assert v.count(old)==1;relation.write_text(v.replace(old,new));changed.append(relation)
    native=ex/'r27_native.rs'
    native.write_text(native.read_text()+'\npub fn check_g(x:&[K;24],case:usize) {r19_channel_ordinary::r81_sparse_scalar_check(x,case);}\n');changed.append(native)
    check=ex/'r27_check.rs';v=check.read_text();needle='        r27_native::check_tensor(&x);'
    assert v.count(needle)==1
    v=v.replace(needle,needle+'\n        r27_native::check_g(&x,case);')
    v=v.replace('    for world in 0..2 {','    println!("R81_SCALAR_G arbitrary=256 selected_basis=271 cache_postconditions=256 old_kernel_retained=true");\n    for world in 0..2 {')
    check.write_text(v);changed.append(check)
test=ex/'r81_square_check.rs';shutil.copy2(here/test.name,test);changed.append(test)
cargo=ex/'performance-host/Cargo.toml'
cargo.write_text(cargo.read_text()+'\n[[bin]]\nname="r81-square-check"\npath="../r81_square_check.rs"\n');changed.append(cargo)
if a.variant in ['powerbasis','compose','privatebasis','scalarg']:
    cargo.write_text(cargo.read_text()+'\n[[bin]]\nname="r81-basis-check"\npath="../r81_basis_check.rs"\n')
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
assert len(m['files'])==(210 if a.variant in ['privatebasis','scalarg'] else 209 if a.variant in ['powerbasis','compose'] else 207)
m['r81_native']={'base_revision':'4b64f97254e18f0338e1ad6229ca8407143aeb2b',
    'variant':a.variant,'control_manifest_sha256':sha(src/'r18-stage.json'),
    'protocol_changed':False,'validation_removed':False,'selected':False,
    'delta':'Guarded square; optionally fixed-arity delayed-reduction dots. Original raw-input fallbacks unchanged.'}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files']),'variant':a.variant}))
