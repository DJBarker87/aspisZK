# Combined gate failure review

The combined import gate is incomplete. Neither attempted replay exited zero;
the two permitted full combined attempts are exhausted. No current gate credit,
CLOSED row, or authoritative ledger delta follows from these attempts.

| Attempt | Result | Wall time | Failure |
| --- | --- | --- | --- |
| NKR_L182 | exit 1 | 14.689863 s | The printed private name contains a numeric component; literal source reference at lines 538–539 is parsed as invalid field/decimal syntax. |
| NKR_L184 | exit 1 | 13.208044 s | Replacing that component by «0» parses, but the elaborator reports unknown identifier/constant for the quoted private name. |

Exact source copies, command/environment/object pins, output, resource receipts,
and source hashes are retained in the respective attempt directories.

## Source visibility and the private proof dependency

NKR_SumCopyFull.lean:556 declares private theorem rows_ext inside
AspisR1.NKR_SumCopyRoot. Its local axioms print at line 560 succeeds
during compilation of that defining module. The public theorem row uses this
helper at line 567. That proves the helper is part of the source proof; it does
not create a public source-level name that a separate importing module can use.

NKR_build_gate.py collects every name printed by focused axioms checks, including
private names, into one roots list. It then emits source #check and #print axioms
commands for every item. This conflates the kernel/raw-audit name of a private
dependency with an exported source-level identifier. Public import does not
recreate the defining module's local private-name resolution.

L182 demonstrates that a printed internal name cannot simply be pasted into
source. L184 demonstrates that quoting its numeric component is insufficient.
In particular, a quoted numeral can denote a string name component rather than
the internal numeric name component. These diagnostics do **not**, by themselves,
prove that the private kernel declaration or its body is absent from the
private-level object/audit environment. The supported conclusion is that the
generated source reference does not resolve in this public import. Private proof
closure must be inspected by the pinned raw walker, not inferred from a guessed
identifier spelling.

## Safe future generator correction

Keep distinct inventories for (1) public declarations checked by source commands
in the combined import and (2) complete kernel roots/dependencies checked by the
hardened private-aware raw audit. A future generator may omit this private
helper's **explicit source command only** if it demonstrably retains private
proof closure in the raw audit: the public row/source roots must remain, the
walk must traverse their private dependencies with the correct internal Name
and pinned private object payload, and fixture/axiom checks must still pass.
Do not remove private roots or dependencies merely to silence an import error.

Alternatively, make the helper public in a new permitted proof module and
recompile its dependent public source root, updating source/object pins and
axioms receipts. That supplies an ordinary source-checkable name. Either route
needs a newly authorized gate attempt; neither changes the outcome of L182 or
L184. No further full combined replay was launched for this review.

Any subsequent direct raw-audit diagnostic is separate evidence. It cannot
replace the missing combined-import/scan gate, waive the two-attempt limit, or
retroactively turn either failed replay into a pass.

NKR_GATE_REPAIR_PROPOSAL.patch is an UNRUN source-check proposal only: remove the two inaccessible private-name commands while retaining the helper in NKR_AUDIT_ROOTS.json and its private closure in the raw audit. It changes no proof and claims no gate result. Regenerate future gates with the same public/private distinction; a newly authorized combined replay and scan remain required.

The own generator has also been repaired prospectively to preserve all private raw roots while emitting public source checks only. It was syntax-checked, not executed; current combined source, failure receipts and gate status are unchanged.
