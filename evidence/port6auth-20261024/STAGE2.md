# Concrete source recovery to Q1

`Port6AUTH_Native.authenticated` calls `Port4B_CallerJoin.accepted` on both SAME
native op13 successes, using a shared model Prepared only through each actual
physical Prepared's explicit `CheckpointBytes4SavedFields.BodyMatches`.
All three roots, wire bytes, node views, sorted keys, duplicate digest handling
and source batch logs are retained. No independently successful second batch
or globally assumed source/model join is substituted. Existing S1/CK provenance
must supply those two BodyMatches on the actual prepare/resume returns.

`Port6AUTH_Recovery.batches` takes the resulting accepted source-ordered batch
logs and, for EACH pos<22, chooses its actual batch, obtains its source slot
path and recovers at `index q kind pos`. All kinds are covered. The cut map is
constructed from the actual log/frame; it is never an arbitrary map assumed
pointwise equal to the candidate. `repeated` proves kind2 payload equality for
any equal parent index, including cross-checkpoint parents, under the SAME
collision exclusion. There is no injectivity assumption on roots.

The FINAL `Port6AUTH_Query.accepted` specializes the containing log to the exact
first source annotation record. Its only collision hypothesis is on the full
source experiment at Q+1161; SourceCut derives the first-pass exclusion and
budget. It consumes the two actual batch returns, actual Q1 geometry calls,
actual constructors, SAME query_loop returns and SAME flushes. It returns:

* the original Q1 saved-ten, continued-twelve and completeState equalities;
* both weight lengths64 and next counters10/22;
* actual recovered maps = actual source compiler builder;
* binary word-builder stability from first to full source annotation record.

The commitment frames/selector predicates are derived, not supplied equalities:
`Port6AUTH_Frames.targets` consumes the source record's own public/proof,
reached parse alignment, and SAME literal matching read. It decodes actual
row0/row2/row30 roots. Sampler read containment supplies their actual membership.
Compiler.frame reconstruction uses the consistent actual source oracle log.
The root predicates concern committed bytes and never identify an arbitrary
whole map by root equality.

## Retained local producers and exact next consumer

* `S2LeadInterface.S2CallerFacts`: literal stored/public/checkpoint bytes, node
  views, source reach/order/account framing, raw digest law. Structure printed
  in final audit; it contains no batch acceptance or source/model output law.
* S1 prepare and `Port6CK` actual op18 resume: roots/queries/BodyMatches on the
  two physical Prepared returns. CK ownership is not duplicated here.
* `Port4B_FoldedCut.model`: actual folded-root copy; foldedInput remains at that
  same local source call boundary. `Port4B_KeyInstall.queries_bound` supplies
  source keys from actual Prepared queries.
* P6Boundary: exact one-parent-call and leaf-step callback gates, printed with
  their definitions. These are local lowering ports, not a whole-verifier join.
* Q1 named arithmetic/domain/decoder/prepare leaves, literal matching read,
  SAME source proof bytes, physical checkpoint continuation and geometry ports
  remain exactly Q1's boundaries. No Session A candidate is edited.
* The driver/trace producer must embed these exact batch programs and the
  exact first-input sampler in the FIRST source record. Merely knowing op13's
  returned Bool is not a theorem of that effect-trace embedding.

The next consumer is the SOURCE `CleanAcceptedModel` in Stage3. Actual query
state and word-map recovery now feed it without authentication circularity.
It still needs source finish/pairing, match0/first-fold and semantic Checks,
plus no-hit composition at the actual source transcript. Existing Port4D's
accepted_finish retains precisely those arithmetic/semantic local ports;
Q1 accumulator equality cannot discharge them by itself. Also instantiate the
all-input1161 source count and unchanged runtime carrier relation. These are
missing source refinement/trace facts; no protocol or owner contract change is
proposed, and the deployed100-bit target remains not yet established.
