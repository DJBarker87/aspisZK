#!/usr/bin/env python3
"""Exact shipped scan helper, with bounded symbolic representation checks.
No OS callback is replaced. These cuts never invoke OS entropy and prove no
whole-owner/client, probability, cleanup, artifact or privacy claim.
"""
from pathlib import Path
import hashlib,json,sys
root=Path(__file__).resolve().parents[2]
source=root/'crates/aspis-prover/src/state_only_entropy.rs'
text=source.read_text()
start=text.index('fn entropy_nonzero32(')
opening=text.index('{',start)
end=opening+1
level=1
while level:
    level += (text[end]=='{')-(text[end]=='}')
    end+=1
helper=text[start:end]
harnesses=r'''
#[cfg(kani)]
mod checks {
    use super::*;
    #[kani::proof] #[kani::unwind(34)]
    fn scan_exact() {
        let a: [u8;32]=kani::any();
        let mut expected=false;
        for i in 0..32 {expected |= a[i]!=0;}
        assert_eq!(entropy_nonzero32(&a),expected);
    }
    #[kani::proof] #[kani::unwind(34)]
    fn scan_zero_iff() {
        let a: [u8;32]=kani::any();
        assert_eq!(!entropy_nonzero32(&a),a==[0;32]);
    }
    #[kani::proof] #[kani::unwind(34)]
    fn scan_reverse() {
        let a: [u8;32]=kani::any();let mut b=[0;32];
        for i in 0..32 {b[31-i]=a[i];}
        assert_eq!(entropy_nonzero32(&a),entropy_nonzero32(&b));
    }
    #[kani::proof] #[kani::unwind(34)]
    fn scan_rotate() {
        let a: [u8;32]=kani::any();let mut b=[0;32];
        let shift:usize=kani::any();kani::assume(shift<32);
        for i in 0..32 {b[(i+shift)%32]=a[i];}
        assert_eq!(entropy_nonzero32(&a),entropy_nonzero32(&b));
    }
    #[kani::proof] #[kani::unwind(34)]
    fn scan_witness() {
        let a: [u8;32]=kani::any();let i:usize=kani::any();
        kani::assume(i<32 && a[i]!=0);
        assert!(entropy_nonzero32(&a));
    }
    #[kani::proof] #[kani::unwind(34)]
    fn single_byte() {
        let mut a=[0;32];let i:usize=kani::any();let b:u8=kani::any();
        kani::assume(i<32);a[i]=b;
        assert_eq!(entropy_nonzero32(&a),b!=0);
    }
    #[kani::proof] #[kani::unwind(66)]
    fn split_roundtrip() {
        let raw:[u8;64]=kani::any();let mut left=[0;32];let mut right=[0;32];
        left.copy_from_slice(&raw[..32]);right.copy_from_slice(&raw[32..]);
        let mut joined=[0;64];joined[..32].copy_from_slice(&left);joined[32..].copy_from_slice(&right);
        assert_eq!(raw,joined);
    }
    #[kani::proof] #[kani::unwind(34)]
    fn split_left() {
        let raw:[u8;64]=kani::any();let mut left=[0;32];
        left.copy_from_slice(&raw[..32]);
        let i:usize=kani::any();kani::assume(i<32);
        assert_eq!(left[i],raw[i]);
    }
    #[kani::proof] #[kani::unwind(34)]
    fn split_right() {
        let raw:[u8;64]=kani::any();let mut right=[0;32];
        right.copy_from_slice(&raw[32..]);
        let i:usize=kani::any();kani::assume(i<32);
        assert_eq!(right[i],raw[i+32]);
    }
    #[kani::proof] #[kani::unwind(34)]
    fn acceptance_exact() {
        let raw:[u8;64]=kani::any();let mut left=[0;32];let mut right=[0;32];
        left.copy_from_slice(&raw[..32]);right.copy_from_slice(&raw[32..]);
        assert_eq!(entropy_nonzero32(&left)&&entropy_nonzero32(&right),
            left!=[0;32]&&right!=[0;32]);
    }
}
'''
output=helper+'\n'+harnesses
out=root/'tools/pv-runjoin-20261026/effect-cuts'
out.mkdir(exist_ok=True)
manifest={'source':str(source.relative_to(root)),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
 'helper_sha256':hashlib.sha256(helper.encode()).hexdigest(),'cut_sha256':hashlib.sha256(output.encode()).hexdigest(),
 'helper_verbatim':True,'stubs':False,'scope':'scan and64-byte split only; no OS/native owner/client claim'}
cargo='[package]\nname="pv-runjoin-effect-cuts"\nversion="0.0.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[profile.release]\nopt-level=3\n[profile.dev]\nopt-level=3\n[workspace]\n'
if '--check' in sys.argv:
    assert (out/'lib.rs').read_text()==output
    assert (out/'Cargo.toml').read_text()==cargo
    assert json.loads((out/'source-pins.json').read_text())==manifest
    print('effect cuts exact helper and pins match')
else:
    (out/'lib.rs').write_text(output);(out/'Cargo.toml').write_text(cargo)
    (out/'source-pins.json').write_text(json.dumps(manifest,indent=2)+'\n')
