fn NHU_preweighted_cut<const N:usize>(packed:&mut [QM31;24],start:usize,values:&[QM31;N],iter:&mut core::ops::RangeInclusive<usize>,log:&mut PackLog){if let Some(group)=iter.next(){
        let lanes: [QM31; 4] = core::array::from_fn(|slot| {
            let source = 4 * group + slot;
            if source >= start && source < start + N {
                values[source - start]
            } else {
                QM31::ZERO
            }
        });
        packed[group] = packed[group].add(pack_cut(&lanes,log));
}}
