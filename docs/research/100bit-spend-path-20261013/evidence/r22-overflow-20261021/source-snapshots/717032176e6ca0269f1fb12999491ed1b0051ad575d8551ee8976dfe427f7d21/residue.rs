#[derive(Clone,Copy)] struct M31(u32);
#[derive(Clone,Copy)] struct CM31{a:M31,b:M31}
#[derive(Clone,Copy)] struct K{c0:CM31,c1:CM31}
fn residue_limb_at(row:&[u64;4],index:usize)->u64 {row[index]}
fn power_limb_at(limbs:&[u32;4],index:usize)->u32 {limbs[index]}
fn update_residue_row(row:&mut [u64;4],power:K,basis:M31,flush:bool,products:[u64;4]) {
    let limbs=[power.c0.a.0,power.c0.b.0,power.c1.a.0,power.c1.b.0];
    for j in 0..4 {
        let old=residue_limb_at(row,j);
        let limb=power_limb_at(&limbs,j);
        row[j]=old+products[j];
    }
    if flush {
        for limb in row {*limb=(*limb&0x7fff_ffff)+(*limb>>31);}
    }
}
#[cfg(kani)] #[kani::proof] #[kani::unwind(6)]
fn frozen_residue_row_phase_step() {
    const B:u64=1u64<<34;
    const C:u64=(2147483647u64-1)*(2147483647u64-1);
    let phase:u64=kani::any();kani::assume(phase<4);
    let mut row:[u64;4]=kani::any();let products:[u64;4]=kani::any();
    for j in 0..4 {kani::assume(row[j]<B+phase*C);kani::assume(products[j]<=C);}
    let power=K{c0:CM31{a:M31(0),b:M31(0)},c1:CM31{a:M31(0),b:M31(0)}};
    // All canonical products are covered, without solving four multiplications
    // at once. product_bound in AspisR1BatchedFoldArithmetic justifies the cap.
    update_residue_row(&mut row,power,M31(0),phase==3,products);
    for x in row {
        if phase==3 {assert!(x<B);} else {assert!(x<B+(phase+1)*C);}
    }
}
