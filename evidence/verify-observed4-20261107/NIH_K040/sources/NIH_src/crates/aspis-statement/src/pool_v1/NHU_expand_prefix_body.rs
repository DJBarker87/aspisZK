fn NHU_expand_prefix_cut(weights:&[QM31;64],prepared:&aspis_core::field::PreparedQm31Multiplier,iter:&mut core::iter::Rev<&mut core::ops::Range<usize>>,log:&mut ExpandLog)->Option<(usize,QM31,QM31)>{if let Some(index)=iter.next(){                let parent = weights[index];
                let right = expand_product(prepared,parent,log);
Some((index,parent,right))}else{None}}
