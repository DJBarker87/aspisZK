# Native fragment interpretation

These local-record checks do not admit any additional ledger row. The additive
NFW validator still admits only powers TX1:197 / TX2:138. All source variants,
resolved offline graphs, unchanged-lock checks, source hashes, deployed features,
resource limits and full outputs are retained per attempt. The KMX patch is
`bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67`.
No field multiplication runs in Kani. No writable static or function-pointer
comparison is introduced. None observers are checked in positive/control/rename
families below; this is not a lifting of the general K-2 quarantine.

- K061/K062: constructor rho call, empty payload, same original harness name.
  Replaces excluded K060 by observing at the selected callback entry without
  building unrelated expected payloads. It does not read every returned field.
- K063: whole constructor return projection timed out; no credit.
- K064: same projection name with all fields captured at Box construction still
  timed out. No unchanged replay. K065/K066 isolate the exact final frozen
  record/Box expression on an arbitrary pre-return state and check all eleven
  field classes. The preceding call-log to pre-return-state association is open.
- K067/K068: scalar oracle adapter's exact local reply, index and log update.
  This validates the fixture/cut, not a shipped arithmetic function.
- K069/K070: exact frozen data-independent alpha/fold block on an arbitrary
  pre-state, all variants, including root32 ++ round1[224] KMX copy behavior.
- K071/K072/K073: program runtime expression with 0..5 parts of length <=32,
  exact slices and returned arbitrary 32-byte reply; reply inversion and corrupt
  argument controls fail. SHA is not executed or assigned a replacement value.
- K074: dense width3717 version timed out and is excluded. K075/K076/K077 use
  dynamically allocated zero-backed windows with one arbitrary byte per backing,
  arbitrary lengths up to u32::MAX, view offsets, aliasing/overlap, selected byte
  observation and arbitrary reply. Both reply inversion and actual argument
  corruption fail. This sparse result is NOT all arbitrary input byte values.
  NFW_BorrowFrame / NFW_ImmutableIO give generic disjoint-memory laws, but a
  complete native representation/source instantiation is still required.
- K078/K079/K080: candidate.prepare's exact frozen source-order body with only
  child operations cut to local records. All first-error positions, six-stage
  call count, heap size14759, split13831/928, original stored source windows,
  public/semantic/scratch argument identity, selected scratch cell and returned
  Box identity are checked. The semantic error fixture here is Public; the
  later all-WireError family broadens it. Children and their byte/model domains
  remain open; this is not a prepare certificate.
- K081/K082/K083: verify_observed's frozen body with local parse/public/begin/
  finish cuts, arbitrary WireError payloads, exact prefix/public identity,
  transcript state32/cursor updates, challenge selection and result identity.
  The Prefix fixture uses empty records; parser validity and successful child
  producer semantics are NOT established by this fixture.
- K084 onward: caller prefixes end exactly at query_loop entry; finish and
  checkpoint production are never entered. Only named child operations are cut.
  TX fixtures deliberately have zero proof backing and opaque geometry/resume
  outputs, so metadata/control checks cannot be promoted to full byte/domain
  correspondence. Read each actual result in NFW_NATIVE_MATRIX.json before use.

Native remaining work is complete child-domain/source association, not another
whole-buffer timeout with a larger cap. Proof-only producer laws and the CLOSED
NFS root already exist, but installing them requires linking these native
records to the same cohort-produced values.
