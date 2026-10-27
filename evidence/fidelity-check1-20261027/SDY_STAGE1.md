# Static stage

Raw Funs SHA256 f4b2d17c061ce7062d64146531788b6448328e656fb6dbd6192f2d61db31a3b5.
No premise removed; no release credit claimed.

All four write paths retain their writes syntactically:
- multiproof.rs:177,182: child1 passed to next_back at raw:1198–1199,1214–1215,1232–1233,1249–1250; final iterator returned through back at1180; enumerate_back/iter_mut_back/to_slice_mut_back at1363–1365; idx/val stores (Rust189–190) explicitly Array.update at1369–1370 (binary1318–1319,1341–1342,1300–1301). Full exact ranges retained in final report after audit.
- verifier.rs:240 row[j] via Array.update raw1939; :243 flush via next_back(some limb1) raw1976–1977; composed back restored into row at2011–2012.
- sampler.rs:93 digit via next_back(some digit1) raw3502–3503; returned back applied at3528–3530. Carry retained at3501,3527,3530.
- verifier.rs:226 *w via next_back(some(i,w)) raw6374–6375, composed back applied through enumerate_back/iter_mut_back at6408–6410.

Whole-file tuple-wildcard scan: SDY_scan.json. Exactly one mutable restoration discard: sampler::low_base_p_digits closure1 raw3611, quotient additionally discarded raw3624. SDX text calls binding line3624; fresh line audit distinguishes binding3611 from division3624. No other wildcard tuple match discards an accessor's restoration callback; unused old values with retained index_mut_back are not losses. Native/emitted fixture checks pending.
