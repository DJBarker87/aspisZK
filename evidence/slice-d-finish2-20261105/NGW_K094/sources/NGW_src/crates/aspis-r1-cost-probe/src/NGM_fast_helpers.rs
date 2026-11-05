use super::*;
pub(crate) fn read(dot:&EbyKDot)->[u64;9]{let a=canonical::NGM_canonical::read(&dot.c0);let b=canonical::NGM_canonical::read(&dot.c1);[a[0],a[1],a[2],a[3],b[0],b[1],b[2],b[3],dot.count as u64]}
pub(crate) fn make(s:[u64;9])->EbyKDot{assert_eq!(usize::BITS,64);EbyKDot{c0:canonical::NGM_canonical::make([s[0],s[1],s[2],s[3]]),c1:canonical::NGM_canonical::make([s[4],s[5],s[6],s[7]]),count:s[8] as usize}}
