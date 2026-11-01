// Owned P6 constructor reference. No compression backend is invoked.
pub fn default_reference() -> ([u32;8],u64,[u8;64],usize) {
    ([0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,
      0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19],0,[0;64],0)
}

// The compression function is an explicit parameter of the plumbing law.
pub trait Compression {
    type State: Copy;
    fn compress(state: Self::State, block: [u8;64]) -> Self::State;
}

pub fn update_reference<C: Compression>(mut state: C::State, mut blocks: u64,
    mut buffer: [u8;64], mut pos: usize, input: &[u8]) -> (C::State,u64,[u8;64],usize) {
    let mut i=0;
    while i<input.len() {
        buffer[pos]=input[i];
        pos+=1;
        if pos==64 {
            state=C::compress(state,buffer);
            blocks=blocks.wrapping_add(1);
            pos=0;
        }
        i+=1;
    }
    (state,blocks,buffer,pos)
}

pub fn finalize_reference<C: Compression<State=[u32;8]>>(mut state: [u32;8],blocks:u64,
    mut buffer:[u8;64],pos:usize) -> ([u8;32],[u32;8],[u8;64]) {
    let bit_len=blocks.wrapping_mul(64).wrapping_add(pos as u64).wrapping_mul(8);
    buffer[pos]=128;
    let mut i=pos+1;
    while i<64 {buffer[i]=0;i+=1;}
    if pos>=56 {state=C::compress(state,buffer);buffer=[0;64];}
    let mut j=0;
    while j<8 {buffer[56+j]=(bit_len >> (8*(7-j))) as u8;j+=1;}
    state=C::compress(state,buffer);
    let mut out=[0;32];
    let mut k=0;
    while k<8 {
        let word=state[k];
        out[4*k]=(word>>24) as u8;
        out[4*k+1]=(word>>16) as u8;
        out[4*k+2]=(word>>8) as u8;
        out[4*k+3]=word as u8;
        k+=1;
    }
    (out,state,buffer)
}

// No destructor is invoked: core is moved into the returned owned snapshot.
pub fn wrap_reference<T>(core:T) -> (T,[u8;64],usize) { (core,[0;64],0) }

// Compression-event trace of SHA-256 padding, independent of either backend.
pub fn padding_reference(mut buffer:[u8;64],pos:usize,bit_len:u64)
    -> ([[u8;64];2],usize,[u8;64]) {
    let mut events=[[0;64];2];let mut count=0;
    buffer[pos]=128;
    let mut i=pos+1;
    while i<64 {buffer[i]=0;i+=1;}
    if pos>=56 {events[count]=buffer;count+=1;buffer=[0;64];}
    let mut j=0;
    while j<8 {buffer[56+j]=(bit_len>>(8*(7-j))) as u8;j+=1;}
    events[count]=buffer;count+=1;
    (events,count,buffer)
}

// The actual batched callback interface: each byte slice is a sequence of
// complete 64-byte blocks, and each call boundary is retained.
pub trait BatchCompression {
    type State:Copy;
    fn compress(state:Self::State,blocks:&[u8])->Self::State;
}
pub fn update_batch_reference<C:BatchCompression>(mut state:C::State,
    mut buffer:[u8;64],pos:usize,input:&[u8]) -> (C::State,[u8;64],usize) {
    let n=input.len();let rem=64-pos;
    if n<rem {
        let mut i=0;while i<n {buffer[pos+i]=input[i];i+=1;}
        return (state,buffer,pos+n);
    }
    let mut start=0;
    if pos!=0 {
        let mut i=0;while i<rem {buffer[pos+i]=input[i];i+=1;}
        state=C::compress(state,&buffer);
        start=rem;
    }
    let full=(n-start)/64;
    let end=start+full*64;
    if full!=0 {state=C::compress(state,&input[start..end]);}
    let left=n-end;
    let mut j=0;while j<left {buffer[j]=input[end+j];j+=1;}
    (state,buffer,left)
}
