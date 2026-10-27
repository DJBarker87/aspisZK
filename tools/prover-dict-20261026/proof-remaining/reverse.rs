//! Owned, loop-free reverse-bits reference; verified against shipped std.
pub fn reverse_reference(mut x:u32)->u32 {
    x=((x>>1)&0x55555555)|((x&0x55555555)<<1);
    x=((x>>2)&0x33333333)|((x&0x33333333)<<2);
    x=((x>>4)&0x0f0f0f0f)|((x&0x0f0f0f0f)<<4);
    x=((x>>8)&0x00ff00ff)|((x&0x00ff00ff)<<8);
    (x>>16)|(x<<16)
}
