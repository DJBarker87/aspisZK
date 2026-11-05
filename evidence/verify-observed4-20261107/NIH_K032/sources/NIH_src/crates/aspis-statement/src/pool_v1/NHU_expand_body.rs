fn NHU_expand_inner_cut<const N:usize>(weights:&mut [QM31;N],prepared:&aspis_core::field::PreparedQm31Multiplier,iter:&mut core::iter::Rev<&mut core::ops::Range<usize>>,log:&mut ExpandLog){if let Some(index)=iter.next(){
                let parent = weights[index];
                let right = expand_product(prepared,parent,log);
                weights[2 * index] = parent.sub(right);
                weights[2 * index + 1] = right;
}}
