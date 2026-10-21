//! Owned source-shaped transitions. No mutable input reference crosses recursion.
pub type Digest = [u8;32];
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub struct Scratch {
    pub idx: [u32;16], pub val: [Digest;16], pub n: usize, pub at: usize,
}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum Row { Stop(Scratch), Next(Scratch,usize,usize) }
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum Level { Stop(Scratch), Done(Scratch) }

/// Caller preconditions: 0 < n <= 16; i < n; w <= i; at <= nodes.len().
/// Missing sibling is an ordinary rejection and preserves the entire scratch.
fn write_parent<H:aspis_core::Digest32>(hash:H,mut s:Scratch,left:Digest,right:Digest,next:usize,at:usize,index:u32,w:usize)->Row {
    let digest=hash.digest(&[&[0x12],&left,&right]);
    s.idx[w]=index/2;s.val[w]=digest;s.at=at;
    Row::Next(s,next,w+1)
}
pub fn binary_step<H:aspis_core::Digest32>(hash:H,s:Scratch,nodes:&[u8],i:usize,w:usize)->Row {
    let index=s.idx[i];let value=s.val[i];
    if i+1<s.n && s.idx[i+1]==index^1 {
        let right=s.val[i+1];
        return write_parent(hash,s,value,right,i+2,s.at,index,w);
    }
    if nodes.len()-s.at<32 {return Row::Stop(s);}
    let sibling=read32(&nodes[s.at..s.at+32]);
    if index&1==0 {write_parent(hash,s,value,sibling,i+1,s.at+32,index,w)}
    else {write_parent(hash,s,sibling,value,i+1,s.at+32,index,w)}
}
pub fn level_rows<H:aspis_core::Digest32>(hash:H,s:Scratch,nodes:&[u8],i:usize,w:usize)->Level {
    if i>=s.n {return Level::Done(Scratch{n:w,..s});}
    match binary_step(hash,s,nodes,i,w) {
        Row::Stop(s)=>Level::Stop(s),
        Row::Next(next,i,w)=>level_rows(hash,next,nodes,i,w),
    }
}
pub fn levels<H:aspis_core::Digest32>(hash:H,s:Scratch,nodes:&[u8],height:u32)->Level {
    if height==0 {return Level::Done(s);}
    match level_rows(hash,s,nodes,0,0) {
        Level::Stop(s)=>Level::Stop(s),
        Level::Done(next)=>levels(hash,next,nodes,height-1),
    }
}
pub fn valid_indices(idx:[u32;16],n:usize,i:usize)->bool {
    if i>=n {return true;}
    if idx[i]>=262144 {return false;}
    if i>0 && idx[i-1]>=idx[i] {return false;}
    valid_indices(idx,n,i+1)
}
/// All rejected runs retain the exact partial scratch arrays.
pub fn verify_owned<H:aspis_core::Digest32>(hash:H,root:Digest,s:Scratch,nodes:&[u8])->(bool,Scratch) {
    if s.n==0 || s.n>16 || !valid_indices(s.idx,s.n,0) || nodes.len()%32!=0 {
        return (false,s);
    }
    let initial=Scratch{at:0,..s};
    match levels(hash,initial,nodes,18) {
        Level::Stop(out)=>(false,out),
        Level::Done(out)=>(out.n==1 && out.idx[0]==0 && out.val[0]==root && out.at==nodes.len(),out),
    }
}
/// Entire leaf insertion step, after the caller has hashed the next sorted leaf.
/// None is duplicate disagreement; arrays are returned unchanged by the caller.
pub fn leaf_step(mut s:Scratch,index:u32,leaf:Digest)->Option<Scratch> {
    if s.n>0 && s.idx[s.n-1]==index {
        if s.val[s.n-1]==leaf {Some(s)} else {None}
    } else {
        s.idx[s.n]=index;s.val[s.n]=leaf;s.n+=1;Some(s)
    }
}

/// The exact four-limb canonical QM31 condition, including little-endian order.
pub fn canonical_word(b:[u8;4])->bool {u32::from_le_bytes(b)<0x7fffffff}
pub fn canonical_qm(b:[u8;16])->bool {
    canonical_word([b[0],b[1],b[2],b[3]]) &&
    canonical_word([b[4],b[5],b[6],b[7]]) &&
    canonical_word([b[8],b[9],b[10],b[11]]) &&
    canonical_word([b[12],b[13],b[14],b[15]])
}
pub fn expand_chunk(c:[u8;16])->[u8;32] {
    [c[0],c[1],c[2],c[3],c[4],c[5],c[6],c[7],c[8],c[9],c[10],c[11],c[12],c[13],c[14],c[15],
     0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
}
pub fn row_shape(row:u8)->Option<(u8,usize)> {
    if row>=27 {None} else if row==2 {Some((1,32))} else if row==14 {Some((3,32))}
    else if row>=15 && row<=24 {Some((2,896))} else if row==25 {Some((4,3712))}
    else if row==26 {Some((5,928))} else {Some((0,0))}
}
/// Generic row recurrence. Endpoints are never expanded into a giant numeral.
pub fn semantic_offsets(row:u8,src:usize,dst:usize)->Option<(usize,usize)> {
    if row>=27 {return Some((src,dst));}
    let size=match row_shape(row) {Some((_,size))=>size,None=>return None};
    let stored=if row>=14 {size/2} else {size};
    semantic_offsets(row+1,src+5+stored,dst+5+size)
}
/// Models check_values' chunks_exact, deliberately ignoring a short suffix.
pub fn check_values(bytes:&[u8])->bool {
    if bytes.len()<16 {return true;}
    let chunk=read16(bytes);
    canonical_qm(chunk) && check_values(&bytes[16..])
}
pub fn expand_rows(bytes:&[u8],mut out:alloc::vec::Vec<u8>)->Option<alloc::vec::Vec<u8>> {
    if bytes.is_empty() {return Some(out);}
    if bytes.len()<16 {return None;}
    let chunk=read16(bytes);
    out.extend_from_slice(&expand_chunk(chunk));
    expand_rows(&bytes[16..],out)
}

pub fn read16(bytes:&[u8])->[u8;16] {[bytes[0],bytes[1],bytes[2],bytes[3],bytes[4],bytes[5],bytes[6],bytes[7],bytes[8],bytes[9],bytes[10],bytes[11],bytes[12],bytes[13],bytes[14],bytes[15]]}

pub fn read32(bytes:&[u8])->[u8;32] {[bytes[0],bytes[1],bytes[2],bytes[3],bytes[4],bytes[5],bytes[6],bytes[7],bytes[8],bytes[9],bytes[10],bytes[11],bytes[12],bytes[13],bytes[14],bytes[15],bytes[16],bytes[17],bytes[18],bytes[19],bytes[20],bytes[21],bytes[22],bytes[23],bytes[24],bytes[25],bytes[26],bytes[27],bytes[28],bytes[29],bytes[30],bytes[31]]}
