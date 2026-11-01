// Correct full-state padding reference. In the two-block case, the native
// object retains the first block; the second is a separate local value.
pub fn padding_retained_reference(mut buffer:[u8;64],pos:usize,bit_len:u64)
    -> ([[u8;64];2],usize,[u8;64]) {
    buffer[pos]=128;
    let mut i=pos+1;while i<64 {buffer[i]=0;i+=1;}
    let mut events=[[0;64];2];
    if pos>=56 {
        events[0]=buffer;
        let mut second=[0;64];let mut j=0;
        while j<8 {second[56+j]=(bit_len>>(8*(7-j))) as u8;j+=1;}
        events[1]=second;
        (events,2,buffer)
    } else {
        let mut j=0;while j<8 {buffer[56+j]=(bit_len>>(8*(7-j))) as u8;j+=1;}
        events[0]=buffer;
        (events,1,buffer)
    }
}
