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
