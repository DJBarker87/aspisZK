//! Proof-only recursive publication. Sorted unique association lists implement
//! the documented ordered-map operations; no timing is part of this owner.
use alloc::vec::Vec;

pub type IndexMap = Vec<(usize, Vec<u8>)>;

pub fn index_tail(table:IndexMap,at:usize,mut out:IndexMap)->IndexMap {
    if at==table.len() {return out;}
    out.push(table[at].clone());
    index_tail(table,at+1,out)
}

/// Replace duplicates, including returning their previous value, as insert does.
/// Precondition for the ordered-map interpretation: table is sorted and unique;
/// at=0 and out=[] at the public boundary.
pub fn index_insert(table:IndexMap,key:usize,value:Vec<u8>,at:usize,mut out:IndexMap)
    ->(IndexMap,Option<Vec<u8>>) {
    if at==table.len() {out.push((key,value));return (out,None);}
    let (k,v)=table[at].clone();
    if key<k {
        out.push((key,value));
        return (index_tail(table,at,out),None);
    }
    if key==k {
        out.push((key,value));
        return (index_tail(table,at+1,out),Some(v));
    }
    out.push((k,v));
    index_insert(table,key,value,at+1,out)
}

pub fn index_get(table:IndexMap,key:usize,at:usize)->Option<Vec<u8>> {
    if at==table.len() {return None;}
    let (k,v)=table[at].clone();
    if key==k {return Some(v);}
    if key<k {return None;}
    index_get(table,key,at+1)
}

/// Entry-or-insert returns whether the lazy source callee must be invoked.
/// The callee is deliberately outside this function, so a hit consumes no coins
/// and performs no field evaluations.
pub fn index_absent(table:IndexMap,key:usize)->bool {
    index_get(table,key,0).is_none()
}

/// Query-order publication uses lookup, preserving repetitions and source order.
pub fn publish_queries(queries:Vec<u32>,opened:IndexMap,at:usize,mut out:Vec<u8>)->Option<Vec<u8>> {
    if at==queries.len() {return Some(out);}
    let bytes=match index_get(opened.clone(),queries[at] as usize,0) {
        Some(v)=>v,None=>return None,
    };
    out.extend_from_slice(&bytes);
    publish_queries(queries,opened,at+1,out)
}

pub type ProgramMap = Vec<(Vec<u8>, [u8;32])>;

/// Lexicographic bytes, including proper prefixes. The cursor is bounded by
/// the shorter input; no iterator or std comparison implementation is extracted.
pub fn byte_order(left:Vec<u8>,right:Vec<u8>,at:usize)->i8 {
    if at==left.len() {return if at==right.len() {0}else{-1};}
    if at==right.len() {return 1;}
    if left[at]<right[at] {return -1;}
    if left[at]>right[at] {return 1;}
    byte_order(left,right,at+1)
}

pub fn program_tail(table:ProgramMap,at:usize,mut out:ProgramMap)->ProgramMap {
    if at==table.len() {return out;}
    out.push(table[at].clone());
    program_tail(table,at+1,out)
}

/// Source insertion replaces even on conflict. The sticky collision flag is
/// retained, so the owner can discard the whole attempt at the native boundary.
pub fn program_insert(table:ProgramMap,key:Vec<u8>,value:[u8;32],at:usize,
    mut out:ProgramMap,collision:bool)->(ProgramMap,bool) {
    if at==table.len() {out.push((key,value));return (out,collision);}
    let (k,v)=table[at].clone();
    let order=byte_order(key.clone(),k.clone(),0);
    if order<0 {
        out.push((key,value));
        return (program_tail(table,at,out),collision);
    }
    if order==0 {
        out.push((key,value));
        return (program_tail(table,at+1,out),collision || v!=value);
    }
    out.push((k,v));
    program_insert(table,key,value,at+1,out,collision)
}

/// Transcript merge is first-conflict, distinct from the sticky Merkle table
/// owner: later transcript entries are never processed after a conflict.
pub fn merge_program(table:ProgramMap,reads:ProgramMap,at:usize)->Option<ProgramMap> {
    if at==reads.len() {return Some(table);}
    let (key,value)=reads[at].clone();
    let (table,conflict)=program_insert(table,key,value,0,Vec::new(),false);
    if conflict {return None;}
    merge_program(table,reads,at+1)
}
