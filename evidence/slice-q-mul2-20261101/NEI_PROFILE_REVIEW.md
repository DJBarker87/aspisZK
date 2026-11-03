# Checked model and deployed wrapping profile

During final review, the field fixtures' explicit
CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true was compared with the frozen Cargo
profile and the C3-BIN profile rulings (2026-10-21, R22, and 2026-10-28, NCS).
The deployed SBF profile wraps; Charon/Aeneas definitions check integer overflow.
All-typed equality of two checked definitions does not prove all-typed native
wrapping fidelity. M31.add(U32::MAX,1) is a concrete distinction. No accepted
protocol counterexample is inferred from this noncanonical input.

The previously generated 66-row candidate was held provisional until the
release profile repair passed. No new trust item is adopted. The repair uses the
existing wrapping FIo_Native definitions and the original canonical call/value
proofs as mathematical lemmas only. No suspended NEB Kani credit is restored.
NEI_ProfileDomain.lean proves the checked/wrapping operator association with
canonical domains where needed, unrestricted raw domains for widened scalar
multiplication/reduction and mixed scalar products, and explicit nominal maps
from the actual E001 carriers. It imports rather than reproves arithmetic.
Every new theorem prints its axioms. Native fixture checks under both profiles
passed with the same actual frozen bodies, controls and inputs.

Caller domains must follow real expressions and sequential returns: the
NEB_FieldDomains/CMCalls/QMCalls/ByRCalls/WideCalls/AdditiveCalls mathematical
witnesses expose these exact arguments. They are not native credit. The fold
packets' NEI_LineDomains and NEI_CircleDomains already prove canonical arguments
and intermediate values, with raw inverse words allowed only at unrestricted
scalar multiplication sites. Canonicality is not assumed for arbitrary inverse
words or all field carriers. Incoming unproved caller edges remain OPEN.

The profile repair is subject to the same capped admission gates. L130 initially waited at exit78/allowed:false; its eventual launch and every
later launch have exit0/allowed:true admission receipts.

L132 replay PASS; L135 symbolic two-child Result/record lemma PASS; L136 all
operator/actual-carrier profile associations PASS, standard axioms only.
L130 reached no proof (legacy import); L131 had an overbroad declaration cut;
L133 was an incomplete draft; L134 hit the kernel memory limit in wide_sub.
The replacement splits the pure Result transport before instantiation and
uses the wrapping model's abstract totality for the raw-input counterexample.
Caps were not raised. Peak RSS of the successful profile file is 5,077,556 KiB;
wall time 2.604 seconds, zero swap. Failed drafts carry no proof credit.
The wrapping WideExact.sub model is the literal two-QM31.sub record wrapper,
needed because that wrapper is not exported by FIo_Native. Its precise body
is visible in NEI_ProfileDomain.lean and associated to actual E001 source.

N015/N016: wrapping-profile native fidelity PASS (20/20 tests), matched
wrong-result controls FAIL as required (20/20). Same source and input hashes
as the checked-profile pair. NEI_PROFILE_TESTS.json passes five additional
domain/profile/association rejection controls; no old native credit used.
