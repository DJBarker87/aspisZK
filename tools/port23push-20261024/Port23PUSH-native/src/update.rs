#[inline(always)]
fn residue_limb_at(row:&[u64;4],index:usize)->u64 {row[index]}
#[inline(always)]
fn power_limb_at(limbs:&[u32;4],index:usize)->u32 {limbs[index]}
#[inline(always)]
fn update_residue_row(row:&mut [u64;4],power:K,basis:M31,flush:bool) {
    let limbs=[power.c0.a.0,power.c0.b.0,power.c1.a.0,power.c1.b.0];
    for j in 0..4 {
        let old=residue_limb_at(row,j);
        let limb=power_limb_at(&limbs,j);
        row[j]=old+u64::from(limb)*u64::from(basis.0);
    }
    if flush {
        for limb in row {*limb=(*limb&0x7fff_ffff)+(*limb>>31);}
    }
}
