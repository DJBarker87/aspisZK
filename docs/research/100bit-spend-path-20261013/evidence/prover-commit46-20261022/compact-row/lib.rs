//! Native compact_semantic row context, with source windows and the common
//! compact_values result kept opaque under the pure std slice/Vec contracts.
use std::ops::{Index,Range};
const CLAIMS:usize=87;const LANES:usize=29;
pub const fn row_shape(row: u8) -> Option<(u8, usize)> {
    match row {
        0 | 1 | 3..=13 => Some((0, 0)),
        2 => Some((1, 32)),
        14 => Some((3, 32)),
        15..=24 => Some((2, 28 * 32)),
        25 => Some((4, (CLAIMS + LANES) * 32)),
        26 => Some((5, LANES * 32)),
        _ => None,
    }
}

#[derive(Clone,Copy,Debug,PartialEq,Eq)] enum CodecError {Length,NonZeroHigh}
#[derive(Clone,Copy,Debug,PartialEq,Eq)] struct Window {start:usize,end:usize}
struct Logical {frame:Window,payload:Window}
impl Index<Range<usize>> for Logical {
 type Output=Window;
 fn index(&self,r:Range<usize>)->&Window {
  if r.start==self.frame.start && r.end==self.frame.end {&self.frame}
  else {assert_eq!(r.start,self.payload.start);assert_eq!(r.end,self.payload.end);&self.payload}
 }
}
#[derive(Clone,Debug,PartialEq,Eq)] struct Buffer {
 appended:[Option<Window>;2],len:usize,callee:Option<Window>,calls:usize,
 state:u8,summary:u8,reject:bool,
}
impl Buffer {
 fn extend_from_slice(&mut self,w:&Window){self.appended[self.len]=Some(*w);self.len+=1;}
}
fn compact_row(row:u8)->bool {row>=14}
fn compact_values(w:&Window,out:&mut Buffer)->Result<(),CodecError> {
 out.callee=Some(*w);out.calls+=1;out.state=out.summary;
 if out.reject {Err(CodecError::NonZeroHigh)} else {Ok(())}
}
fn native_row(logical:&Logical,out:&mut Buffer,row:u8,mut at:usize)->Result<usize,CodecError> {
        let size = row_shape(row).ok_or(CodecError::Length)?.1;
        out.extend_from_slice(&logical[at..at + 5]);
        at += 5;
        if compact_row(row) {
            compact_values(&logical[at..at + size], out)?;
        } else {
            out.extend_from_slice(&logical[at..at + size]);
        }
        at += size;
        Ok(at)
}
fn size(row:u8)->Option<usize> {
 const S:[usize;27]=[0,0,32,0,0,0,0,0,0,0,0,0,0,0,32,896,896,896,896,896,896,896,896,896,896,3712,928];
 S.get(row as usize).copied()
}
fn reference(logical:&Logical,out:&mut Buffer,row:u8,at:usize)->Result<usize,CodecError> {
 let n=size(row).ok_or(CodecError::Length)?;
 out.extend_from_slice(&logical.frame);
 if row>=14 {compact_values(&logical.payload,out)?;} else {out.extend_from_slice(&logical.payload);}
 Ok(at+5+n)
}
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(128)] fn compact_row_context() {
  let row:u8=kani::any();let at:usize=kani::any();kani::assume(at<=13831);
  let n=size(row).unwrap_or(0);
  let logical=Logical{frame:Window{start:at,end:at+5},payload:Window{start:at+5,end:at+5+n}};
  let out=Buffer{appended:[None,None],len:0,callee:None,calls:0,state:kani::any(),summary:kani::any(),reject:kani::any()};
  let mut actual=out.clone();let mut expected=out;
  let a=native_row(&logical,&mut actual,row,at);
  let b=reference(&logical,&mut expected,row,at);
  assert_eq!(a,b);assert_eq!(actual,expected);
 }
}
