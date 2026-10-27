# LPq stage 1: scalar and complex nominal ports

Accepted L004 and L005: LPq_ScalarPorts and LPq_FieldPorts. Six exact scalar
namespace equalities, four complete complex-operation Result maps and four
canonical total-success ports. These connect the existing frozen FIo arithmetic
to XRy's cached release namespace, preserving each input/output word. Existing
LPi arithmetic theorems supply totality/canonicality; no multiplication is
proved in Kani or re-established as a new arithmetic specification.

No caller domain, security premise, trust item or artifact changes. Canonical
inputs remain the preconditions of the four total-success ports. The graph
maps have no canonicality precondition and retain complete Results.

L004: exit0, wall1.8245613109902479s, peak4770132KiB, swap0.
L005: exit0, wall1.884899273980409s, peak4774364KiB, swap0.
Exact full revision, source hashes, selected dependency objects, cgroup and
axioms are in each receipt.json. Every new theorem has #print axioms; only
propext/Classical.choice/Quot.sound occur. LPq_LIBRARY_PIN.json pins the selected
Aeneas objects. Focused stage only; not a full manifest or leaf closure.

L002 inspected the actual definitions but rejected a #print namespace typo;
L003's failed nominal reduction/recursion shape was split into L004 scalar
rewrites and L005 composition. All failed diagnostics and source inputs are
retained, with error-recovery sorryAx excluded. No option/cap was raised.
L001's missing companion runner was a preflight failure before Lean, documented
in LPq_RUNNER_CHANGE.md; shared infrastructure was never changed.

Remaining: QM/wide ports, powers7, decoder, concrete six-loop construction,
seven weighting steps, whole same-carrier Result and empty digest-attempt log.
No headline premise removed. Prepared_claim remains OPEN.
