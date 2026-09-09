//! Opt-in research design change: selected transfer output positivity.
//! No production feature enables this module. The legacy mask generator's
//! draw order is retained; its active-row1014/c3 draw is discarded before C1.
//! New transcript framing binds this adapter, not a claim of unchanged ZK.
use super::*;
use aspis_statement::{pool_v1::*, StateOnlyTraceFoundation};
#[cfg(not(v8_performance_sbf))]
#[path="selected_transfer_zero.rs"] mod zero_fixture;

pub const ROW: usize = 1014;
pub const COL: usize = 3;
pub const LANE: usize = 94;
pub const PROFILE: &[u8] = b"AV8/positive-transfer/active-cell-overwrite/lane94/v1";

pub fn mask_cells() -> Vec<aspis_statement::TraceCell> {
    let mut cells=pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
    assert_eq!(cells.len(),3803);
    assert_eq!(cells.iter().filter(|c|c.row as usize==ROW && c.column as usize==COL).count(),1);
    cells.retain(|c|c.row as usize!=ROW || c.column as usize!=COL);
    assert_eq!(cells.len(),3802); cells
}
fn fingerprint(cells:&[aspis_statement::TraceCell])->u64 {
    let mut h=0xcbf2_9ce4_8422_2325u64;
    for c in cells {for b in c.row.to_le_bytes().into_iter().chain([c.column]) {
        h=(h^u64::from(b)).wrapping_mul(0x100000001b3);
    }} h
}
pub fn descriptor()->Vec<u8>{
    // Verifier-derived canonical bytes only; no prover-supplied digest.
    let mut d=PROFILE.to_vec();
    d.extend(V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING);
    d.extend((ROW as u16).to_le_bytes());d.push(COL as u8);d.push(LANE as u8);
    let old=pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
    d.extend(fingerprint(&old).to_le_bytes());
    d.extend(fingerprint(&mask_cells()).to_le_bytes());
    d.extend((3802u16).to_le_bytes());
    d
}
pub fn absorb(t:&mut Transcript){t.absorb(label::PROFILE,&descriptor());}
pub fn entropy_binding(binding:&[u8;32])->[u8;32]{
    hash(&[b"AV8/positive-transfer/legacy-mask-stream/v1",&descriptor(),binding])
}
pub fn install(trace:&mut StateOnlyTraceFoundation)->Result<(),Error>{
    if trace.c1.iter().any(|c|c.len()!=1024){return Err(Error::Shape);}
    let active=pool_v1_pair_forest_copy_active_rows_v1().map_err(|_|Error::Shape)?;
    if !active.contains(&(ROW as u16)){return Err(Error::Shape);}
    let r=trace.c1[1][ROW];let c=trace.c1[1][ROW+1];
    if r==M31::ZERO || c==M31::ZERO{return Err(Error::Domain);}
    trace.c1[COL][ROW]=r.mul(c).inv();
    Ok(())
}
#[cfg(not(v8_performance_sbf))]
pub fn case_compilation(case:&str,baseline:&PoolV1PairForestMergedC1CompilationV1,
    p:PoolV1PrivateTransferPublicV1,mut w:PoolV1PairForestPrivateTransferWitnessV1)
    ->(PoolV1PrivateTransferPublicV1,PoolV1PairForestMergedC1CompilationV1){
    match case {
        "honest"=>return(p,baseline.clone()),
        "recipient_zero"=>{w.recipient.value=0;w.change.value=1000;},
        "change_zero"=>{w.recipient.value=1000;w.change.value=0;},
        _=>panic!("unknown predeclared positivity case"),
    }
    zero_fixture::rewrite_outputs(baseline,p,w)
}
pub fn residual(claims:&[K;84])->K{
    claims[1].mul(claims[28+1]).mul(claims[COL]).sub(K::ONE)
}
pub fn selector(z:&[K;10])->K{
    z.iter().enumerate().fold(K::ONE,|a,(j,x)|a.mul(
        if (ROW>>(9-j))&1==1 {*x} else {K::ONE.sub(*x)}))
}
pub fn equality(z:&[K;10],zc:&[K;10])->K{
    z.iter().zip(zc).fold(K::ONE,|p,(a,b)|{
        let ab=a.mul(*b);p.mul(K::ONE.sub(*a).sub(*b).add(ab).add(ab))})
}
pub fn composition_delta(claims:&[K;84],z:&[K;10],theta:K)->K{
    // Source lane94 = packed group23, limb2; after four Poseidon lanes it
    // has theta exponent27. Do not treat extension-valued packing as casts.
    let weighted=selector(z).mul(residual(claims));
    let packed=corelib::field::qm31_pack_base4(&[K::ZERO,K::ZERO,weighted,K::ZERO]);
    let t2=theta.square();let t4=t2.square();let t8=t4.square();let t16=t8.square();
    t16.mul(t8).mul(t2).mul(theta).mul(packed)
}
pub fn terminal_delta(claims:&[K;84],z:&[K;10],theta:K,zc:&[K;10],eta:K)->K{
    eta.mul(equality(z,zc).mul(composition_delta(claims,z,theta)))
}

#[cfg(not(v8_performance_sbf))]
pub fn layout_control(){
    let old=pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();let new=mask_cells();
    assert_eq!(fingerprint(&old),pool_v1_pair_forest_relation_free_mask_fingerprint_v1().unwrap());
    let active=pool_v1_pair_forest_copy_active_rows_v1().unwrap();
    assert!(active.contains(&(ROW as u16)));
    for col in 0..16 {
        let dep=|cells:&[aspis_statement::TraceCell]|cells.iter().filter(|c|
            c.column as usize==col && !active.contains(&c.row)).last().unwrap().row;
        assert_eq!(dep(&old),dep(&new));assert_eq!(dep(&new),1023);
    }
    // Independent source-shaped Horner assembly for arbitrary QM31 residuals,
    // including zero theta. This is differential arithmetic, not soundness.
    for seed in 0usize..32 {
        let theta=if seed==0{K::ZERO}else{K{c0:CM31::new(M31(seed as u32),M31(7)),c1:CM31::new(M31(11),M31((seed+1)as u32))}};
        let z=std::array::from_fn(|j|sc(((ROW>>(9-j))&1)as u32));
        let claims=std::array::from_fn(|i|K{c0:CM31::new(M31((seed+i+1)as u32),M31(3)),c1:CM31::new(M31(5),M31(9))});
        let mut lanes=[K::ZERO;29];
        lanes[27]=corelib::field::qm31_pack_base4(&[K::ZERO,K::ZERO,residual(&claims),K::ZERO]);
        let expected=lanes.iter().rev().fold(K::ZERO,|a,v|a.mul(theta).add(*v));
        assert_eq!(composition_delta(&claims,&z,theta),expected);
    }
    println!("POSITIVE_LAYOUT old_cells=3803 new_cells=3802 old_fp={:016x} new_fp={:016x} active_reserved=true unchanged_dependents=16 descriptor_bytes={} packing_controls=32",fingerprint(&old),fingerprint(&new),descriptor().len());
}
