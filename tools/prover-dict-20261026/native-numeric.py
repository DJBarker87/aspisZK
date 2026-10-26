from pathlib import Path
r=Path(__file__).resolve().parents[2];p=r/'crates/aspis-r1-cost-probe/src/r1_wire.rs';s=p.read_text();assert 'mod pdict_numeric_contracts' not in s
ks=['isize','i64','i32','i16','i8','usize','u64','u32','u16','u8']
s+='''
#[cfg(kani)]
mod pdict_numeric_contracts {
    use sha2::digest::typenum::{Unsigned,Bit,UInt,B0,B1,consts::*};
    fn numeric<U:Unsigned,B:Bit>() {
'''
for k in ks:
 s+=f'''        assert_eq!(UInt::<U,B>::to_{k}(), (B::to_u8() as {k}) | U::to_{k}().wrapping_shl(1));
        assert_eq!(UInt::<U,B>::{k.upper()}, (B::U8 as {k}) | U::{k.upper()}.wrapping_shl(1));
'''
s+='''    }
    #[kani::proof]
    fn numeric_source_recursion() {
'''
for n in [0,1,2,4,8,16,32,64,128,256,512]:s+=f'        numeric::<U{n},B0>(); numeric::<U{n},B1>();\n'
s+='    }\n}\n';p.write_text(s)
