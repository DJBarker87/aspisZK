"""New actual parser projections not covered by retained NHC Some fields."""
from pathlib import Path
import sys,json
E=Path(__file__).resolve().parent;sys.dont_write_bytecode=True;sys.path.insert(0,str(E))
from NIE_native_prepare import stage,attrs

def prepare(control):
 assert control in ['none','delegate','native','close','delegated','frame']
 mutation={'none':'','delegate':'parsed.has_delegate = !parsed.has_delegate;','native':'parsed.is_native = !parsed.is_native;','close':'parsed.has_close_authority = !parsed.has_close_authority;','delegated':'parsed.delegated_amount ^= 1;','frame':'data[query] ^= 1;'}[control]
 src='''use super::*;
ATTR
#[kani::proof]
#[kani::unwind(166)]
fn association() {
 let mut data:[u8;165]=kani::any();
 data[72..76].copy_from_slice(&1u32.to_le_bytes());
 data[109..113].copy_from_slice(&1u32.to_le_bytes());
 data[129..133].copy_from_slice(&1u32.to_le_bytes());
 data[108]=1;
 let query:usize=kani::any();kani::assume(query<165);
 let before=data[query];
 let expected=u64::from_le_bytes([data[121],data[122],data[123],data[124],data[125],data[126],data[127],data[128]]);
 let mut parsed=parse_legacy_token_account_v1(&data).unwrap();
 MUTATION
 assert!(parsed.has_delegate);
 assert!(parsed.is_native);
 assert!(parsed.has_close_authority);
 assert!(parsed.delegated_amount==expected);
 assert!(data[query]==before);
}
'''.replace('ATTR',attrs()).replace('MUTATION',mutation)
 stage('programs/aspis-pool/src/vault.rs',src,'actual full-backing token parser flags/delegated amount and readonly frame','positive' if control=='none' else 'negative','Every 165-byte token backing with option tags exactly1 at72/109/129 and state1 at108; all other bytes unrestricted apart from those bytes; no None zero loop is executed. Every frame query0..164.','Full production custody parser/caller PacketDomains, None-case zero-loop association, child/CPI/balance/authority frames remain OPEN. Prior NHC field/Some observations are reused, not rerun as new claims.',dict(control=control,reused='NHC_K086..089, NHC_K110..115 and NHC_CustodyWindows by SHA citation; only flags/delegated/full readonly frame are new assertions'))
if __name__=='__main__':prepare(sys.argv[1])
