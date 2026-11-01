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
