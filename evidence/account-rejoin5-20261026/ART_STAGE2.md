# Stage 2: failed-syscall coverage

ART_PartialProgram retains each actual syscall status; its failed call asks for
one ghost bookkeeping answer (never given to native continuation) then rejects.
The returned raw Log keeps failure/divergence instead of inventing a successful
answer. ART_QueryAgreement.compatible needs ONLY agreement at successful issued
calls; unlike ARS, no ReturnsOnly certificate is required.

ART_Coverage.execution / ART_Outcome.native / ART_Cost.exact /
ART_OriginalLaw.exact prove exact original partial-native outcomes and attempted
cost, including TX1 rejection, TX2 rejection, repeated queries, and adaptive
second choice. The existing extraction boundary is used verbatim. Coverage
certificate is a query-agreement criterion, not an adopted top trust item.

ART_AccountAccepted.exact and ART_RuntimeAccepted.exact prove, for EVERY H,
that accepted failure-aware executions equal the existing ideal account, full
log and outcome included. ART_Runtime.rejected gives zero runtime failure mass
for every rejection. ART_PrefixCoupling.source/cost retain the failed call and
prove actual attempts form an ideal prefix; they never charge an unissued ideal
suffix as original work. ART_RejectedDigest exhibits the one-actual/two-ideal
case without dropping the actual failure.

ART_Carrier.projection covers proof/public bytes on all failure-aware outcomes;
checkpoint preserves the existing SAME supported entry's physical 1768-byte CP
via SCJ/CPH. No checkpoint field is invented in RunView.

F2's syscall-rejection exclusion is repaired at the literal source/experiment
interface. This does NOT prove all-world bank support, original unconditioned
ROM law, or discharge actual Rc10 binding/finish antecedents. The new partial
interpreter is source-only proof instrumentation, not changed shipped code.
