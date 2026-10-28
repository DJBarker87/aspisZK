// Safe references. No Kani, unsafe code, observer, or function pointer.
pub fn row_shape_ref(row:u8)->Option<(u8,usize)>{
 match row {
  0|1|3..=13=>Some((0,0)),2=>Some((1,32)),14=>Some((3,32)),
  15..=24=>Some((2,896)),25=>Some((4,3712)),26=>Some((5,928)),_=>None,
 }
}
pub fn compact_row_ref(row:u8)->bool{row>=14}
pub fn slot_offset_ref(slot:usize)->usize{
 let sizes=[146usize,146,128,172,172,150];
 let mut i=0;let mut at=28359;
 while i<slot {at+=32*sizes[i];i+=1;}at
}
#[derive(Clone,Copy,PartialEq,Eq)]
pub enum RefError{InvalidRow,Length(u8),Tag(u8),NonCanonical(u8,usize)}
pub fn validate_ref(row:u8,payload:&[u8])->Result<(),RefError>{
 let mut i=0;
 while i<payload.len()/32 {
  let mut j=0;
  while j<8 {
   let at=32*i+4*j;
   let word=(payload[at] as u32)|((payload[at+1] as u32)<<8)|((payload[at+2] as u32)<<16)|((payload[at+3] as u32)<<24);
   if word>=2147483647 || (j>=4 && word!=0){return Err(RefError::NonCanonical(row,i));}
   j+=1;
  }i+=1;
 }Ok(())
}
pub fn parse_record_ref(row:u8,record:&[u8])->Result<&[u8],RefError>{
 let (tag,size)=row_shape_ref(row).ok_or(RefError::InvalidRow)?;
 if record.len()!=5+size{return Err(RefError::Length(row));}
 if record[0]!=tag{return Err(RefError::Tag(row));}
 let size_wire=(record[1] as usize)|((record[2] as usize)<<8)|((record[3] as usize)<<16)|((record[4] as usize)<<24);
 if size_wire!=size{return Err(RefError::Length(row));}
 let payload=&record[5..];if row>=14 {validate_ref(row,payload)?;}Ok(payload)
}
pub fn parse_at_ref(bytes:&[u8],row:u8,offset:usize)->Result<(&[u8],usize),RefError>{
 let length=5+row_shape_ref(row).unwrap().1;
 let end=offset+length;
 let framed=bytes.get(offset..end).ok_or(RefError::Length(row))?;
 parse_record_ref(row,framed)?;Ok((framed,end))
}
