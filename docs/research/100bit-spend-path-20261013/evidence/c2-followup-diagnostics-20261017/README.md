# Retained negative C2 extraction diagnostics

All three are `REJECTED_DIAGNOSTIC`, not accepted extraction cones or production
changes. None establishes a useful emitting source-equivalent1f proposal.
The exact original caller/build attempts remain in c2-owned-host-20261017.

| Diagnostic | Charon exit/wall/RSS KiB | Aeneas exit/wall/RSS KiB | First observed blocker |
|---|---|---|---|
| owned-lanes | 0/.811s/196288 | 2/1.008s/161040 | `InterpJoin.ml:1680`, packing width branch |
| copy-helper | 0/.403s/183908 | 2/.603s/70928 | `SymbolicToPureAbs.ml:1313`, whole c2 body |
| owned-prefix | 0/.609s/194460 | 2/1.208s/134992 | `InterpAbs.ml:191`, whole constructor |

Every attempt used base source deb68369ba3ad7cc6706dc24b6503fac1cbe942b and the
pinned compiler binaries,6GiB high/8GiB max/swap0. All measured process swaps
were0; exact commands, wall/RSS, caps, aggregate reservations, source/runner/tool
pins, inputs and logs are in the archive. No Lean ran for these compiler-only
attempts; `#print axioms` is not applicable. Every LLBC has `has_errors=false`,
but every Aeneas attempt failed. No generated source is accepted from them.

Transformations, recorded explicitly in each input source-pins.json:

- owned-lanes moves the unchanged indices into branch-local filled+copy calls
  producing an owned Vec. It passes the initial borrowed index-slice join and
  reaches packing. It has not been adopted or proved source-equivalent.
- copy-helper moves the original copy loop into a private helper, substituting
  only self.messages→messages, and replaces the caller loop by its helper call.
  It still fails the caller. No source adoption is justified.
- owned-prefix additionally moves the unchanged complete leaves allocation+
  packing segment into an opaque private helper returning the allocated leaves.
  The original Tree::new remains at its original struct-literal position.
  This passes the earlier packing branch site but still fails. It is not a
  checked source-refinement result and retains the earlier diagnostic encoder
  signature weakening; it is not a production constructor implementation.

Archive followup-diagnostics.tar.gz SHA
5ff6e4ea749b7e13c035209495bc4ab8526e3b468473880a1102cbb22f788b5b has69files,
all pinned by followup-members.json. These failed inputs must not be treated
as additional accepted re-pin roots. No source/native/SBF/runtime/Lean/live
worktree or module change accompanied this diagnostic work.
