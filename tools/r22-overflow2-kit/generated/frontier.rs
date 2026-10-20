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
fn sorted_suffix(a:&[u32;16],i:usize,n:usize)->bool {(0<i || 0>=n || (a[0]<(1<<18))) && (1<i || 1>=n || (a[1]<(1<<18) && (1==i || a[0]<a[1]))) && (2<i || 2>=n || (a[2]<(1<<18) && (2==i || a[1]<a[2]))) && (3<i || 3>=n || (a[3]<(1<<18) && (3==i || a[2]<a[3]))) && (4<i || 4>=n || (a[4]<(1<<18) && (4==i || a[3]<a[4]))) && (5<i || 5>=n || (a[5]<(1<<18) && (5==i || a[4]<a[5]))) && (6<i || 6>=n || (a[6]<(1<<18) && (6==i || a[5]<a[6]))) && (7<i || 7>=n || (a[7]<(1<<18) && (7==i || a[6]<a[7]))) && (8<i || 8>=n || (a[8]<(1<<18) && (8==i || a[7]<a[8]))) && (9<i || 9>=n || (a[9]<(1<<18) && (9==i || a[8]<a[9]))) && (10<i || 10>=n || (a[10]<(1<<18) && (10==i || a[9]<a[10]))) && (11<i || 11>=n || (a[11]<(1<<18) && (11==i || a[10]<a[11]))) && (12<i || 12>=n || (a[12]<(1<<18) && (12==i || a[11]<a[12]))) && (13<i || 13>=n || (a[13]<(1<<18) && (13==i || a[12]<a[13]))) && (14<i || 14>=n || (a[14]<(1<<18) && (14==i || a[13]<a[14]))) && (15<i || 15>=n || (a[15]<(1<<18) && (15==i || a[14]<a[15])))}
#[kani::requires(indices.len()<=16)]
#[kani::ensures(|r:&bool| !*r || (!indices.is_empty() && (0>=indices.len() || (indices[0]<(1<<18))) && (1>=indices.len() || (indices[1]<(1<<18) && indices[0]<indices[1])) && (2>=indices.len() || (indices[2]<(1<<18) && indices[1]<indices[2])) && (3>=indices.len() || (indices[3]<(1<<18) && indices[2]<indices[3])) && (4>=indices.len() || (indices[4]<(1<<18) && indices[3]<indices[4])) && (5>=indices.len() || (indices[5]<(1<<18) && indices[4]<indices[5])) && (6>=indices.len() || (indices[6]<(1<<18) && indices[5]<indices[6])) && (7>=indices.len() || (indices[7]<(1<<18) && indices[6]<indices[7])) && (8>=indices.len() || (indices[8]<(1<<18) && indices[7]<indices[8])) && (9>=indices.len() || (indices[9]<(1<<18) && indices[8]<indices[9])) && (10>=indices.len() || (indices[10]<(1<<18) && indices[9]<indices[10])) && (11>=indices.len() || (indices[11]<(1<<18) && indices[10]<indices[11])) && (12>=indices.len() || (indices[12]<(1<<18) && indices[11]<indices[12])) && (13>=indices.len() || (indices[13]<(1<<18) && indices[12]<indices[13])) && (14>=indices.len() || (indices[14]<(1<<18) && indices[13]<indices[14])) && (15>=indices.len() || (indices[15]<(1<<18) && indices[14]<indices[15]))))]
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
