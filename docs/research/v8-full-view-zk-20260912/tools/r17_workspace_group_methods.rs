// Caller-owned flat workspace holds (normal,carry) pairs for all 64 groups.
impl Kernel {
    pub(super) fn prefix_into(&self,values:&[K],sums:&mut[K])->[K;4] {
        assert!(values.len()<=1024);assert!(sums.len()>=128);
        sums[..128].fill(K::ZERO);
        for (g,row) in values.chunks(16).enumerate() {
            sums[2*g]=row.iter().enumerate().fold(K::ZERO,|s,(j,&v)|s.add(v.mul(self.normal[j])));
            sums[2*g+1]=row.iter().take(3).enumerate().fold(K::ZERO,|s,(j,&v)|s.add(v.mul(self.carry[j])));
        }
        self.contract(|j|(sums[2*j],sums[2*j+1]))
    }
    pub(super) fn binary_masks_into(&self,masks:&[u16;64],sums:&mut[K])->[K;4] {
        assert!(sums.len()>=128);
        for (g,&mask) in masks.iter().enumerate() {
            let mut normal=K::ZERO;let mut carry=K::ZERO;
            for j in 0..16 {if mask&(1<<j)!=0 {
                normal=normal.add(self.normal[j]);
                if j<3 {carry=carry.add(self.carry[j]);}
            }}
            sums[2*g]=normal;sums[2*g+1]=carry;
        }
        self.contract(|j|(sums[2*j],sums[2*j+1]))
    }
}
