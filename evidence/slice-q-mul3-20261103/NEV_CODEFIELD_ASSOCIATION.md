# Accumulation's small outside-slice constructor

`CodeField<WideExact>::from_m31`, frozen scalar.rs line 89, is absent from
slice Q's function list but is reached by its accumulation row at line 285.
It is the small leaf boundary already recorded by NEI. The root native check
executes the actual frozen trait method under deployed verifier features;
it does not compare a replacement Rust reference to itself.

E001 extracts that actual trait path and all reached constructor definitions,
with NCO tool pins and byte-identical frozen core sources. L010/L011 compile
its emitted Types/Funs. No external template or axiom is imported. L012 proves
the complete emitted result on ALL raw U32 inputs: first coordinate is
`word mod P`, other seven are zero. It reuses S1's generic remainder law.
L017 connects the emitted extraction wrapper to that exact trait result.

K030/K031 are an original-name PASS/FAIL pair, exact KMX copy mitigation,
unchanged frozen lock before/after, frozen resolved graph and all-crate
feature receipts, no static or function-pointer state. Native assertions
observe every coordinate through arbitrary `observed < 8`. The failure
flips the asserted selected coordinate, retaining all other configuration.

For the adopted NBF callback, normalization is identity only on a canonical
word. L013 derives this precondition from the SAME returned production basis
and SAME indexed read, using NBF_BasisDomain.read_canonical; it does not
introduce canonicality as an unproved constructor assumption. The result
maps losslessly to the NBF eight-word carrier.

`NEV_codefield_validate.py` checks the extraction hashes, receipts, original
native/control configuration, admitted scopes, permitted axioms, and the
actual constructor use. Its `NEV_CODEFIELD_PACKET.json` is an auxiliary
CLOSED-CONDITIONAL packet. This is NOT a new Q row or accumulation closure.
The remaining accumulation native/control, full Result/state/effect and
callee-domain edges remain OPEN. P6/D188 semantic transport option A is
retained as a tool-trust clarification, not removed; compiler/library,
allocator, runtime and source-to-ELF qualifications remain. No shipped source
changed and no historical ELF evidence is reattributed to a changed body.
