use crate::field::{M31, QM31 as K, WideExact as E};
use crate::transport::Variant;

pub const SEMANTIC_BYTES:usize=12903+29*32;
pub const HEADER:usize=16;
#[cfg(not(feature = "private-leaf-salts"))]
pub const INITIAL_QUERY_BYTES:usize=480+128+2*6*7*32;
#[cfg(feature = "private-leaf-salts")]
pub const INITIAL_QUERY_BYTES:usize=480+128+64+2*6*7*32;
#[cfg(not(feature = "private-leaf-salts"))]
pub const SECOND_QUERY_BYTES:usize=4*32+6*7*32;
#[cfg(feature = "private-leaf-salts")]
pub const SECOND_QUERY_BYTES:usize=4*32+32+6*7*32;
pub const CHECKPOINT_FIXED:usize=16+32*3+64+32*4+16+88+160+64+32*2+16+32;

#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum Error { Parse,Semantic,Transcript,Relation,Merkle,Query,Checkpoint,Allocation }

pub struct View<'a> {
    pub variant:Variant,pub semantic:&'a[u8],pub y1:&'a[u8],pub inactive:E,
    pub round0:&'a[u8],pub folded_root:Option<&'a[u8;32]>,pub round1:&'a[u8],
    pub final_message:&'a[u8],pub query_bytes:&'a[u8],
}

struct ViewShape {
    variant:Variant, inactive:E,
    semantic_start:usize, semantic_end:usize,
    y1_start:usize, y1_end:usize,
    round0_start:usize, round0_end:usize,
    folded_root_start:Option<usize>,
    round1_start:usize, round1_end:usize,
    final_start:usize, final_end:usize, query_start:usize,
}

fn echeck(b:&[u8],k:bool)->Result<(),Error> {
    for c in b.chunks_exact(32) {let x=E::from_le_bytes(c).ok_or(Error::Parse)?;if k&&x.c1()!=K::ZERO {return Err(Error::Parse);}}
    Ok(())
}

fn folded_offsets(at: usize, folded: bool) -> (Option<usize>, usize, usize, usize) {
    if folded { (Some(at), at+32, at+256, 256) }
    else { (None, at, at, 0) }
}

impl<'a> View<'a> {
    pub fn proof_bytes(v:Variant)->usize {HEADER+SEMANTIC_BYTES+29*32+32+7*32+if v.folds()==2 {32+7*32}else{0}+v.final_len()*32+22*(INITIAL_QUERY_BYTES+if v.folds()==2 {SECOND_QUERY_BYTES}else{0})}
    #[inline(never)]
    fn parse_shape(bytes:&[u8])->Result<ViewShape,Error> {
        #[cfg(not(feature = "private-leaf-salts"))]
        let magic = b"R1P2COST";
        #[cfg(feature = "private-leaf-salts")]
        let magic = b"R1P3COST";
        if bytes.len()<HEADER||&bytes[..8]!=magic||bytes[9..16].iter().any(|&x|x!=0) {return Err(Error::Parse);}
        let v=Variant::from_tag(bytes[8]).ok_or(Error::Parse)?;
        if bytes.len()!=Self::proof_bytes(v) {return Err(Error::Parse);}
        let mut at=HEADER;
        let semantic_start=at;at+=SEMANTIC_BYTES;let semantic_end=at;
        let y1_start=at;at+=29*32;let y1_end=at;
        let inactive=E::from_le_bytes(&bytes[at..at+32]).ok_or(Error::Parse)?;at+=32;
        let round0_start=at;at+=7*32;let round0_end=at;
        let (folded_root_start,round1_start,round1_end,folded_used)=folded_offsets(at,v.folds()==2);
        at+=folded_used;
        let final_start=at;at+=v.final_len()*32;let final_end=at;
        let query_start=at;
        Ok(ViewShape{variant:v,inactive,semantic_start,semantic_end,y1_start,y1_end,round0_start,round0_end,folded_root_start,round1_start,round1_end,final_start,final_end,query_start})
    }
    #[inline(never)]
    pub fn parse(bytes:&'a[u8])->Result<Self,Error> {
        let shape=Self::parse_shape(bytes)?;
        let folded_root:Option<&'a[u8;32]>=match shape.folded_root_start {
            Some(start)=>Some(bytes[start..start+32].try_into().map_err(|_|Error::Parse)?),
            None=>None,
        };
        let out=Self{
            variant:shape.variant,
            semantic:&bytes[shape.semantic_start..shape.semantic_end],
            y1:&bytes[shape.y1_start..shape.y1_end],
            inactive:shape.inactive,
            round0:&bytes[shape.round0_start..shape.round0_end],
            folded_root,
            round1:&bytes[shape.round1_start..shape.round1_end],
            final_message:&bytes[shape.final_start..shape.final_end],
            query_bytes:&bytes[shape.query_start..],
        };
        echeck(out.y1,true)?;
        echeck(out.round0,false)?;
        if out.variant.folds()==2 {echeck(out.round1,false)?;}
        echeck(out.final_message,false)?;
        query_checks(out.query_bytes, out.variant)?;
        Ok(out)
    }
    pub fn query(&self,i:usize)->&'a[u8] {let width=INITIAL_QUERY_BYTES+if self.variant.folds()==2 {SECOND_QUERY_BYTES}else{0};&self.query_bytes[i*width..(i+1)*width]}
}



// Extraction-candidate helper: exact query-validation loop moved from View::parse.
fn query_checks(query_bytes: &[u8], variant: Variant) -> Result<(), Error> {
        let width=INITIAL_QUERY_BYTES+if variant.folds()==2 {SECOND_QUERY_BYTES}else{0};
        for i in 0..22 {
            let q=&query_bytes[i*width..(i+1)*width];
            for s in 0..4 {
                for l in 0..26 {M31::from_le_bytes(q[s*120+l*4..s*120+l*4+4].try_into().unwrap()).ok_or(Error::Parse)?;}
                K::from_le_bytes(&q[s*120+104..s*120+120]).ok_or(Error::Parse)?;
                for l in 0..2 {K::from_le_bytes(&q[480+s*32+l*16..480+s*32+l*16+16]).ok_or(Error::Parse)?;}
            }
            if variant.folds()==2 {echeck(&q[INITIAL_QUERY_BYTES..INITIAL_QUERY_BYTES+128],false)?;}
        }
        Ok(())
}

pub fn view_parse_probe(bytes: &[u8]) -> Result<View<'_>, Error> { View::parse(bytes) }
