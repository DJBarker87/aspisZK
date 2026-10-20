const MAX_BATCH:usize=16;const LEAF_BITS:u32=18;
#[derive(Clone,Copy,kani::Arbitrary)] enum Arity{Two,Eight}
impl Arity {

pub const fn bits(self) -> u32 {
        match self {
            Self::Two => 1,
            Self::Eight => 3,
        }
    }

pub const fn width(self) -> usize {
        1 << self.bits()
    }

pub const fn levels(self) -> u32 {
        LEAF_BITS / self.bits()
    }
}
fn sorted_suffix(a:&[u32;16],i:usize,n:usize)->bool {
    (i..n).all(|k| a[k]<(1<<18) && (k==i || a[k-1]<a[k]))
}
#[kani::requires(indices.len()<=16)]
#[kani::ensures(|r:&bool| !*r || (!indices.is_empty() && (0..indices.len()).all(|k|indices[k]<(1<<18) && (k==0 || indices[k-1]<indices[k]))))]
fn well_formed(indices: &[u32]) -> bool {
    !indices.is_empty()
        && indices.len() <= MAX_BATCH
        && indices.windows(2).all(|w| w[0] < w[1])
        && indices.iter().all(|&i| i < 1 << LEAF_BITS)
}

fn index_at(indices: &[u32; MAX_BATCH], index: usize) -> u32 {
    indices[index]
}
#[kani::proof_for_contract(well_formed)] #[kani::unwind(18)]
fn validator() {let a:[u32;16]=kani::any();let n:usize=kani::any();kani::assume(n<=16);well_formed(&a[..n]);}
#[kani::requires(n<=16 && i<n && sorted_suffix(&level,i,n))]
#[kani::ensures(|j:&usize| i<*j && *j<=n && *j-i<=arity.width() && (*j==n || index_at(&level,*j)>>arity.bits()>index_at(&level,i)>>arity.bits()))]
fn group_end(arity:Arity,level:[u32;16],i:usize,n:usize)->usize {
let parent = index_at(&level, i) >> arity.bits();
            let mut j = i;
            while j < n && index_at(&level, j) >> arity.bits() == parent {
                j += 1;
            }
j
}
#[kani::proof_for_contract(group_end)] #[kani::unwind(18)]
fn suffix_group() {group_end(kani::any(),kani::any(),kani::any(),kani::any());}
#[kani::proof] #[kani::unwind(18)]
#[kani::stub_verified(well_formed)] #[kani::stub_verified(group_end)]
fn validated_group_caller(){
    let mut a:[u32;16]=kani::any();let n:usize=kani::any();kani::assume(n<=16);
    if !well_formed(&a[..n]) {return;}
    let i:usize=kani::any();kani::assume(i<n);
    let w:usize=kani::any();kani::assume(w<=i);
    let arity:Arity=kani::any();
    let j=group_end(arity,a,i,n);
    let siblings=arity.width()-(j-i);
    a[w]=index_at(&a,i)>>arity.bits();
    assert!(siblings<=7 && w+1<=j && j<=n);
}
