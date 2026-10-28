from pathlib import Path
E=Path(__file__).resolve().parent;s=(E/'NBO_native.rs.txt').read_text()
a=s.index('fn NBO_actual_query_reject() {');b=s.index('\n}',a)+2
case=s[a:b].replace('fn NBO_actual_query_reject()', 'fn NBO_full_proof_actual_reject()')
case=case.replace('proof:[u8;832]','proof:[u8;57607]').replace('NBO_PROOF=proof.as_ptr();','NBO_EVENT=1;NBO_PROOF=proof.as_ptr().add(crate::compact::OFF_OPENINGS+next*crate::compact::OPENING);')
inverse='Vec::from(['+','.join('['+','.join('M31(kani::any())' for _ in range(5))+']' for _ in range(10))+'])'
line='Vec::from(['+','.join('M31(kani::any())' for _ in range(10))+'])'
case=case.replace('inverses:Vec::new(),line_z:Vec::new()',f'inverses:{inverse},line_z:{line}')
s+='''#[kani::proof]
#[kani::unwind(65536)]
#[kani::stub(crate::fast_dots::four_dots,NBO_dots)]
#[kani::stub(crate::verifier::QueryGeometry::for_query,NBO_inverse)]
#[kani::stub(crate::verifier::circle_fold_with_inverses,NBO_circle)]
#[kani::stub(crate::weights::field,NBO_field)]
#[kani::stub(crate::verifier::line_fold_with_inverses,NBO_never_line)]
'''+case+'\n'
(E/'NBO_native.rs.txt').write_text(s)
