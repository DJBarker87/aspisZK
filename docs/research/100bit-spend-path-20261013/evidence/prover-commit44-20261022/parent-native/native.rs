fn native(table:&Table,coins:&mut Coins,level:&Level,root:[u8;32],depth:u32,p:usize,reads:&mut usize,next:&mut Next,kids_here:&mut Kids) {
            let kids=core::array::from_fn(|s|level.get(&(2*p+s)).copied().unwrap_or_else(||coins.coin()));
            let answer=if depth+1==multiproof::LEAF_BITS {root} else {coins.coin()};
            multiproof::binary_parent(ProgramOne{table,answer},&kids[0],&kids[1]);*reads+=1;
            next.insert(p,answer);kids_here.insert(p,kids);
}
