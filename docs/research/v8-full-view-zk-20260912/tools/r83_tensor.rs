// Included inside r19_channel_ordinary. Only canonical complementary pairs
// enter the specialization; all other inputs use the unchanged general path.
#[inline(never)]
fn r83_fill_tensor(pairs:&[[K;2];10],block1:[K;4],storage:&mut[K],blocks:&mut[K]) {
    assert_eq!(storage.len(),80);assert_eq!(blocks.len(),20);
    let canonical=|v:&K|[v.c0.a.0,v.c0.b.0,v.c1.a.0,v.c1.b.0]
        .iter().all(|&x|x<corelib::field::P);
    if !pairs.iter().flatten().chain(block1.iter()).all(canonical)
        || !pairs.iter().all(|p|p[0].add(p[1])==K::ONE) {
        return fill_tensor_support(pairs,block1,storage,blocks);
    }
    for r in 0..5 {
        if r==1 {blocks[4..8].copy_from_slice(&block1);continue;}
        let x=pairs[2*r][1];let y=pairs[2*r+1][1];let xy=x.mul(y);
        blocks[4*r]=K::ONE.sub(x).sub(y).add(xy);
        blocks[4*r+1]=x.sub(xy);blocks[4*r+2]=y.sub(xy);blocks[4*r+3]=xy;
    }
    // First tensor block sums to one; block1 may have any canonical sum.
    for high in 0..4 {
        let mut sum=K::ZERO;
        for low in 0..3 {let v=blocks[low].mul(block1[high]);storage[4*high+low]=v;sum=sum.add(v);}
        storage[4*high+3]=block1[high].sub(sum);
    }
    // The 4x4 tensor table has known row and column sums. Nine products
    // determine its sixteen entries, without inversion or exceptional cases.
    let mut common=[K::ZERO;16];
    for high in 0..3 {
        let mut sum=K::ZERO;
        for low in 0..3 {let v=blocks[8+low].mul(blocks[12+high]);common[4*high+low]=v;sum=sum.add(v);}
        common[4*high+3]=blocks[12+high].sub(sum);
    }
    for low in 0..4 {common[12+low]=blocks[8+low].sub(common[low].add(common[4+low]).add(common[8+low]));}
    let mut sum=K::ZERO;
    for j in 0..15 {let v=common[j].mul(blocks[16]);storage[16+j]=v;sum=sum.add(v);}
    storage[31]=blocks[16].sub(sum);
    for j in 16..30 {storage[16+j]=common[j&15].mul(blocks[17]);}
    storage[79]=common[15].mul(blocks[19]);
}

#[cfg(not(target_os="solana"))]
pub(super) fn r83_tensor_check(x:&[K;24]) {
    for complementary in [false,true] {
        let pairs=core::array::from_fn(|i|if complementary {[K::ONE.sub(x[i]),x[i]]}else{[x[2*i],x[2*i+1]]});
        let block=core::array::from_fn(|i|x[20+i]);
        let mut old=[K::ONE;80];let mut actual=old;
        let mut old_blocks=[K::ONE;20];let mut actual_blocks=old_blocks;
        fill_tensor_support(&pairs,block,&mut old,&mut old_blocks);
        r83_fill_tensor(&pairs,block,&mut actual,&mut actual_blocks);
        assert_eq!(actual,old,"tensor values, including untouched poison slots");
        assert_eq!(actual_blocks,old_blocks,"tensor blocks");
    }
}
