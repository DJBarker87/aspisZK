from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;f=Path('design/PV-OWNER-PACKET-20261027.md');s=f.read_text();marker='## Decision requested (D474, 2026-10-29)';tail=s[s.index(marker):];old=hashlib.sha256(tail.encode()).hexdigest()
s=s.replace('[recount 8 pins](../evidence/privacy-recount-20261026/recount8/pins.json)','[recount 9 pins](../evidence/privacy-recount-20261026/recount9/pins.json)')
s=s.replace('The following decisions/actions remain open.','''The open items at recount9 are the client diagnostic design (D474), the
headline observation interface (D478), the successful-user/zero-change domain,
paired throttled timing, V242 compiler cohort, release features and constant-time
decoding, N7 custody, SHA-NI, DOITM implementation and client scope. No adoption
of D474 or D478 is recorded at the pins. D474 recommends fixed diagnostics,
no backtrace capture and a fixed aborting panic hook, with reviewed client
change, ELF checks, repin and timing re-run. D478 recommends an event-retaining
headline and joint simulator composition. The decision texts below are unchanged.

The present headline remains conditional on RustRealRefinement and sees only
the returned Result. It does not establish joint privacy for D159's ordered
outputs, failure/divergence prefixes and timing. The prove_wall_seconds source
witness and conditional clock theorem show why Result-fibre recovery cannot
supply that observation on a good completed path. No paired native non-bad
execution was certified and no witness-dependent timing leak is claimed.
Experimental EVHD is separate and unadopted. Its later progress is outside the
recorded snapshot.

The diagnostic line is paused after diag12 pending D474; no deployed DIAG link
was discharged. V239 is parked after ownp, with SourceDense proved and four
deployed links open. Rjdec/rj4idb are parked with conditional decoder/factorization
results. L1 counts and the publication theorem have compiled skeletons with
open native/joint links; op227 and L2E remain in progress at their pinned heads.
These decompositions organize proof work and do not close the endpoint.

The following decisions/actions remain open.''')
s=s.replace('The source conclusion retains its\ncanonical codec, pool/deployment and readiness meaning;', 'The source conclusion retains its\ncanonical codec, pool/deployment and readiness meaning;')
a=s.index('Runjoin34–46 adds body,');b=s.index('The owner domain choice remains open',a)
s=s[:a]+'''Runjoin34–54 adds body, serialization, weight-constructor, opening and publication
composition results. RUNJOIN_PUBLISH_COMPACT is conditional on named links:
R24Sampler is proved; CommonSample, BackendInput, FinishContext, QueryAppend,
NodeAppend and PublishOrder remain open in the recorded runjoin54 result.
Native/toRP composition remains unfinished. V244's reference and installed
callback nonvacuity is now proved at model/original-carrier scope; its complete
native binding, D188 and library coverage remain open. The op227 hypothesis is
not discharged.
'''+s[b:]
a=s.index('The options are a total representation');b=s.index('K-1 and K-2 are evidence corrections',a)
s=s[:a]+'''D474 and D478 now state the representation and implementation choices explicitly.
The lead recommends D474(C) and D478(1). The complete D159 observer remains the
target; neither narrowing nor a client change has been approved at these pins.
Public transaction/context determinism remains a useful verifier-side route.
Client diagnostics have conditional option-B event laws and three typed DIAG
skeletons, with fifteen named links. None of the deployed producer links was
fully discharged through diag12. The reusable syscall, buffering and partial
write laws retain EINTR, errors and pending-delivery prefixes; they are not
complete std I/O, format, capture, cleanup or honest joint-distribution bindings.

The inspected op227 fmt glue is panic-only on the scoped honest source route,
with model complete-Result panic exclusions. This does not exclude every panic
or diagnostic in the deployed client. Error/formatter operands, logger levels,
captured PCs and frames, TLS, unwinding and native writes still need actual
bindings and original-L1 coupling. OptionB makes environmental outcomes public
subject to V400's witness-independence P obligation; it does not make secret
operands, whole prefixes or elapsed time public inputs by declaration.

No admitted same-public witness pair showing different honest diagnostics was
established, and no universal native occurrence/content independence was proved.
V178/V181 remain suspended despite the repaired rdeac focused replay62002.
Allocator failure and post-world remain under rdea-1 with their explicit public
failure-event obligation. D348 has both client and verifier coverage remaining.
Evidence: LOG D425/D432/D456/D458–D479 and recount9/CORRECTIONS9.md.

'''+s[b:]
a=s.index('K-1 and K-2 are evidence corrections');b=s.index('## Decision: prover timing evidence',a)
s=s[:a]+'''K-1 and K-2 remain evidence corrections. Exact KMX patches and matched failing
controls govern copy-dependent Kani credit; function-pointer forms remain
quarantined. Recount9 confirms scoped restorations V229/V230 under own-2 triple-prime
with the deployed-configuration harness label, V256/V257 after the exact-path
replay, and V260/V265/V217 under own-1. V213's compliant binding, restoring law
and focused audit restore its scoped source/Result credit; seventeen aggregate
consumers remain unfinished. The36 b3p6 raw-model associations are reclassification
within existing tool trust, not V244 closure. No endpoint premise is removed.
The V2 proof-only source supersession is resolved under h5''; it changes no
statement and does not settle the separate observation-carrier finding.

'''+s[b:]
s=s.replace('## Release checklist and nonvacuity update, recount8','## Release checklist and nonvacuity update, recount9')
a=s.index('The merged pv-2tnv partial result');b=s.index('FixturePdaRuntime remains deferred',a)
s=s[:a]+'''The pv-2tnv partial result constructs a byte-derived transfer13 public statement,
canonical matching witness and append/payment/lane associations. Rj4idb proves
the byte-pinned typed caller equality and consumes V047's fibre without that
equality hypothesis. Live native record/handle binding and FixturePdaRuntime
remain; a joint native headline instance is not obtained.
'''+s[b:]
a=s.index('The full-withdrawal/zero-change domain, paired throttled timing,');b=s.index(marker,a)
s=s[:a]+'''The pending choices are listed in the refreshed summary above. Client toolchain
selection, D188 narrowing, failure-signal optionB and the three-field T remain
approved. O_EXCL, durable nonce-store persistence, world/ownership and process
state remain proof/adequacy obligations. Source membership, leaf restoration
and skeleton compilation do not establish the deployed privacy target.

'''+s[b:]
assert s[s.index(marker):]==tail
f.write_text(s);(P/'owner-text-preservation9.json').write_text(json.dumps(dict(D474_D478_sha256_before=old,D474_D478_sha256_after=hashlib.sha256(tail.encode()).hexdigest(),byte_identical=True),indent=2)+'\n')
