# Segment evidence (in progress)

P: K003 default solver TIMEOUT95.31s; K004 CaDiCaL TIMEOUT92.41s. Changed backend Kissat K005 PASS2.90s, K006 inverse FAIL2.87s. No unchanged timeout rerun. Integer limb arithmetic only, no field multiplication Kani proof. Reference/model product law NKJ_Scalar.product (L005 standard axioms) proves extracted result equals natural product and coherent checked product on canonical inputs.
A: K007 PASS, K008 inverse FAIL.
C: K009 PASS, K010 inverse FAIL; exact verbatim prelude, returned decoded caches.
W: K011 PASS, K012 inverse FAIL; arbitrary i/j/prestate/updated value, complete array equality.
Copy: K013/014 sums and K015/016 cache positive/inverse pairs; exact KMX patch hash bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.
Record fidelity: K017..021 sums; K022..026 cache: weak pass, inverse fail, real-body assertion pass, unimplied assertion under stub_verified fail, modifies violation fail. Final review pending.

No field stub, writable static, Option<fn>, timeout increase or native closure credit is present. Every receipt records own NKJ_target and frozen offline graph/unchanged lock before/after Kani.
