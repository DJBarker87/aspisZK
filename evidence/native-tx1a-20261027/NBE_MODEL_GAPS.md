# NBE checked target inspection

The models are the installed source-shaped computations, not translations of
the native mutable-borrow body. The source pins are NBE_SOURCE_ASSOCIATION.json.

- MultiproofConeP6Composition.NodeGate quantifies all arbitrary row states
  satisfying RowDomain (n<=16, i<=n, w<=i, cursor<=physical length), not only
  sorted states. Its source row must preserve the complete scratch, stop and
  next state and exact physical digest addresses. The native verifier helper
  callbacks alone do not discharge this field. Native in-place writes must
  additionally be associated to this row and the height/root/admission code.
- Port4B_KeyInstall.build uses modulo262144 in its query interpretation;
  callers must prove native queries<262144 before identifying the key array.
  Native helper/step checks do not by themselves establish the array loop
  association or install the inherited sort recurrence.
- Port4B_CountInstall.nodeCount is a mathematical count recurrence; its accepted
  theorem does not prove the frozen node_count implementation. The native
  nested count scan still requires its own local iteration/induction join.
- Port3_NativeBatchBody retains actual Result and mutable scratch carriers.
  Replacing its three calls by independently successful calls would lose
  early rejection and chronological effects. No such assumption is introduced.

No XRn_Join kit or stand-in is used. LPt's locally CLOSED prepared_claim is reused
only as inherited status, not a new result. No parser law is taken from an
unmerged lane. When needed, NBE_ParserOpeningDomain names this exact dependency:
parse/caller shape supplies the SAME57607-byte proof allocation and its22
832-byte opening slices, and canonical prepared query words<262144. This is
an OPEN caller dependency until composed with the owning lane on research.
