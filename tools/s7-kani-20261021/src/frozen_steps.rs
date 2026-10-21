// Exact frozen loop-body fragments, wrapped for independent per-step Kani.
fn frozen_update_limb(row:&mut [u64;4],power:K,basis:M31,j:usize) {
    let limbs=[power.c0.a.0,power.c0.b.0,power.c1.a.0,power.c1.b.0];
        let old=residue_limb_at(row,j);
        let limb=power_limb_at(&limbs,j);
        row[j]=old+u64::from(limb)*u64::from(basis.0);
}
fn frozen_fold_limb(limb:&mut u64) {*limb=(*limb&0x7fff_ffff)+(*limb>>31);}
fn frozen_group(flat_inverse:&[M31],i:usize)->[M31;5] {core::array::from_fn(|j|flat_inverse[5*i+j])}
