use std::vec::Vec; const LEAF_BITS:u32=18; const MAX_BATCH:usize=16; #[derive(Clone,Copy)] enum Arity { Two,Eight }

impl Arity {
    #[inline(always)]
    pub const fn bits(self) -> u32 {
        match self {
            Self::Two => 1,
            Self::Eight => 3,
        }
    }
    #[inline(always)]
    pub const fn width(self) -> usize {
        1 << self.bits()
    }
    #[inline(always)]
    pub const fn levels(self) -> u32 {
        LEAF_BITS / self.bits()
    }
}

fn well_formed(indices: &[u32]) -> bool {
    !indices.is_empty()
        && indices.len() <= MAX_BATCH
        && indices.windows(2).all(|w| w[0] < w[1])
        && indices.iter().all(|&i| i < 1 << LEAF_BITS)
}

fn index_at(indices: &[u32; MAX_BATCH], index: usize) -> u32 {
    indices[index]
}

pub fn generic_count(arity: Arity, indices: &[u32]) -> Option<usize> {
    if !well_formed(indices) {
        return None;
    }
    let mut level = [0u32; MAX_BATCH];
    level[..indices.len()].copy_from_slice(indices);
    let mut n = indices.len();
    let mut count = 0;
    for _ in 0..arity.levels() {
        let mut w = 0;
        let mut i = 0;
        while i < n {
            let parent = index_at(&level, i) >> arity.bits();
            let mut j = i;
            while j < n && index_at(&level, j) >> arity.bits() == parent {
                j += 1;
            }
            count += arity.width() - (j - i);
            level[w] = parent;
            w += 1;
            i = j;
        }
        n = w;
    }
    Some(count)
}

pub fn generate(
    arity: Arity,
    indices: &[u32],
    mut node: impl FnMut(u32, u32) -> [u8; 32],
) -> Option<Vec<u8>> {
    let count = generic_count(arity, indices)?;
    let mut out = Vec::with_capacity(32 * count);
    let mut level: Vec<u32> = indices.to_vec();
    for depth in 0..arity.levels() {
        let mut next = Vec::new();
        let mut i = 0;
        while i < level.len() {
            let parent = level[i] >> arity.bits();
            for slot in 0..arity.width() as u32 {
                let child = (parent << arity.bits()) | slot;
                if i < level.len() && level[i] == child {
                    i += 1;
                } else {
                    out.extend_from_slice(&node(depth, child));
                }
            }
            next.push(parent);
        }
        level = next;
    }
    (out.len() == 32 * count).then_some(out)
}

struct BinaryTree {levels:Vec<Vec<[u8;32]>>}

impl BinaryTree {
pub(crate) fn multiproof(&self,indices:&[u32])->Option<Vec<u8>> {
        let bits=LEAF_BITS as usize;

        let count=host_count(indices)?;
        let out=Vec::with_capacity(32*count);
        let level=indices.to_vec();
        let out=multiproof_levels(self,out,level,0,bits);
        if out.len()==32*count {Some(out)} else {None}
    }
}

fn multiproof_levels(tree:&BinaryTree,out:Vec<u8>,level:Vec<u32>,depth:usize,bits:usize)->Vec<u8> {
    if depth==bits {return out;}
    let (out,next)=multiproof_level(&tree.levels[depth],&level,out);
    drop(level);
    multiproof_levels(tree,out,next,depth+1,bits)
}

fn multiproof_level(nodes:&[[u8;32]],level:&[u32],mut out:Vec<u8>)->(Vec<u8>,Vec<u32>) {
    let mut next=Vec::new();let count=level.len();let mut i=0;
    while i<count {
        let parent=level[i]>>1;
        (out,i)=multiproof_child(nodes,level,out,i,parent<<1);
        (out,i)=multiproof_child(nodes,level,out,i,(parent<<1)|1);
        next.push(parent);
    }
    (out,next)
}

fn multiproof_child(nodes:&[[u8;32]],level:&[u32],mut out:Vec<u8>,i:usize,child:u32)->(Vec<u8>,usize) {
    if i<level.len() && level[i]==child {(out,i+1)}
    else {out.extend_from_slice(&nodes[child as usize]);(out,i)}
}

fn check_indices(indices:&[u32])->Option<()> {
    if indices.is_empty() || indices.len()>MAX_BATCH {return None;}
    let mut i=0;
    while i<indices.len() {
        if indices[i]>=1<<LEAF_BITS || (i>0 && indices[i-1]>=indices[i]) {return None;}
        i+=1;
    }
    Some(())
}

fn count_levels(level:[u32;MAX_BATCH],n:usize,depth:u32,count:usize,bits:u32)->usize {
    if depth==bits {return count;}
    let (level,n,missing)=count_level(level,n);
    count_levels(level,n,depth+1,count+missing,bits)
}

fn count_level(mut level:[u32;MAX_BATCH],n:usize)->([u32;MAX_BATCH],usize,usize) {
    let mut i=0;let mut w=0;let mut missing=0;
    while i<n {
        let (parent,take)=count_parent(&level,i,n);
        level[w]=parent;w+=1;i+=take;missing+=2-take;
    }
    (level,w,missing)
}

fn count_parent(level:&[u32;MAX_BATCH],i:usize,n:usize)->(u32,usize) {
    let parent=level[i]>>1;
    let take=if i+1<n && level[i+1]>>1==parent {2} else {1};
    (parent,take)
}

fn host_count(indices:&[u32])->Option<usize> {
    check_indices(indices)?;
    let mut level=[0u32;MAX_BATCH];
    level[..indices.len()].copy_from_slice(indices);
    Some(count_levels(level,indices.len(),0,0,LEAF_BITS))
}


fn address(depth:u32,index:u32)->[u8;32] {
 let mut a=[0;32];a[0]=depth as u8;
 a[1..5].copy_from_slice(&index.to_le_bytes());a
}
fn reference(mut indices:Vec<u32>,levels:u32)->Vec<(u32,u32)> {
 let mut reads=vec![];
 for depth in 0..levels {
  let mut next=vec![];let mut i=0;
  while i<indices.len() {
   let x=indices[i];let parent=x/2;
   let mut end=i+1;
   while end<indices.len()&&indices[end]/2==parent {end+=1;}
   if end-i==1 {reads.push((depth,if x%2==0 {x+1} else {x-1}));}
   next.push(parent);i=end;
  }
  indices=next;
 }
 reads
}
fn check(tree:&BinaryTree,indices:&[u32])->usize {
 let expected=reference(indices.to_vec(),18);let mut calls=vec![];
 let got=generate(Arity::Two,indices,|d,i|{calls.push((d,i));address(d,i)}).unwrap();
 assert_eq!(calls,expected);
 let bytes:Vec<u8>=expected.iter().flat_map(|&(d,i)|address(d,i)).collect();
 assert_eq!(got,bytes);assert_eq!(tree.multiproof(indices).unwrap(),bytes);
 assert_eq!(generic_count(Arity::Two,indices),Some(expected.len()));
 assert_eq!(host_count(indices),Some(expected.len()));1
}
fn main() {
 let tree=BinaryTree{levels:(0..=18).map(|depth|(0..(1u32<<(18-depth))).map(|index|address(depth,index)).collect()).collect()};
 let mut checks=0;
 // Every nonempty subset of sixteen nearby leaves, with all sharing patterns.
 for mask in 1..(1u32<<16) {
  let idx:Vec<u32>=(0..16).filter(|i|mask&(1u32<<i)!=0).collect();
  checks+=check(&tree,&idx);
 }
 let mut state=0x7654_3210_fedc_ba98u64;
 for case in 0..10000 {
  let len=1+case%16;let mut idx=vec![];
  while idx.len()<len {
   state^=state<<13;state^=state>>7;state^=state<<17;
   let x=(state as u32)&((1<<18)-1);
   if !idx.contains(&x) {idx.push(x);}
  }
  idx.sort();checks+=check(&tree,&idx);
 }
 for bad in [vec![],vec![0,0],vec![1,0],vec![1<<18],(0..17).collect()] {
  assert!(generate(Arity::Two,&bad,|_,_|panic!("invalid input reached payload")).is_none());
  assert!(tree.multiproof(&bad).is_none());
 }
 // Exercise generic eight-way branch as a separate finite control.
 let mut eight=0;
 for idx in [vec![0],vec![0,1],vec![0,7,8,63,64,262143]] {
  let mut reads=vec![];
  let got=generate(Arity::Eight,&idx,|d,i|{reads.push((d,i));address(d,i)}).unwrap();
  assert_eq!(got.len(),32*reads.len());assert_eq!(generic_count(Arity::Eight,&idx),Some(reads.len()));eight+=1;
 }
 println!("{{\"binary_inputs\":{},\"eight_way_controls\":{},\"invalid_controls\":5,\"failed\":0}}",checks,eight);
}

