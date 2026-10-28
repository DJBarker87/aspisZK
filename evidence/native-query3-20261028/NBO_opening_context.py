from pathlib import Path
E=Path(__file__).resolve().parent;s=(E/'NBO_native.rs.txt').read_text()
a=s.index('fn NBO_prefix_case(){');b=s.index('\n}',a)+2
case=s[a:b].replace('fn NBO_prefix_case()', 'fn NBO_full_proof_prefix_case()')
case=case.replace('proof:[u8;832]','proof:[u8;57607]').replace('NBO_PROOF=proof.as_ptr();','NBO_EVENT=1;NBO_PROOF=proof.as_ptr().add(crate::compact::OFF_OPENINGS+next*crate::compact::OPENING);')
s+='\n'+case+'''
#[kani::proof]
#[kani::unwind(65536)]
#[kani::stub(crate::fast_dots::four_dots,NBO_dots)]
#[kani::stub(crate::verifier::QueryGeometry::for_query,NBO_inverse)]
#[kani::stub(crate::verifier::circle_fold_with_inverses,NBO_circle)]
#[kani::stub(crate::weights::field,NBO_field)]
fn NBO_full_proof_prefix(){NBO_full_proof_prefix_case()}
'''
(E/'NBO_native.rs.txt').write_text(s)
