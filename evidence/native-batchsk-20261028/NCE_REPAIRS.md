# Own input repairs

NCE_L001 failed elaboration: a do-let line needed an explicit statement separator,
and `prefix` is reserved syntax. Added separators and renamed that binder to
`before`. No proposition, precondition or resource limit was weakened.
The failed attempt's printed sorryAx comes from elaboration error recovery and
is excluded; no proof pass is claimed for it.

At the ten-minute launcher review the local PID had already exited; the guard
assertion prevented any signal from being sent. The existing submission was
then recovered normally, with its failed compile receipt. No process was killed
and no submission was duplicated.

NCE_L002 retained a layout error in the second inline do expression; both
expressions now use ordinary multiline do blocks. Its first root audited
standard-only, but the failing module and second root are excluded.

The own final pin collector exceeded the shell argv limit before executing
its read-only command. It now transmits the identical expected pin JSON as
zlib/base64 and performs the same hash and terminal-runner checks. This
collector repair runs no proof and weakens no validation.

Recovery L005: one Bool test needed explicit `decide` at the conjunction,
and a multiline record-update field needed an unbroken expression. Fixed
own new source syntax/elaboration only. The predicate is logically identical;
no native domain or validation was weakened. All L005 sorryAx error-recovery
output is excluded. No timeout or memory kill occurred.

L006: the inherited scan-group width refers to its proved endpoint; explicitly
rewrite the endpoint before applying its width bounds. This is a proof repair,
not a changed conclusion. L007 also refines the prospective native scan cut to
the reached finite machine domain (n<=16, cursor<=n, live keys and parent below
262144), and proves preservation at each step. The previous unrestricted Nat
callback was a mathematical interface, not a native certificate; it is not
retained as a proposed Rust requirement. No native fact has passed.

L007's two domain-preservation failures were unreduced record projections in
omega. Expose the scalar goal with `change` before arithmetic. The finite
domain and theorem statements are unchanged; failed recovery axioms excluded.

L011: the opening continuation retained a reducible tuple `let` after the
successful read. Reduce that tuple explicitly before rewriting the induction
hypothesis. This changes no statement, address, domain or carrier. The failed
module's recovery axioms are excluded; read_byte itself audited standard-only.

L012: SSH exit255 after submission. The existing wrapper immediately tried
read-only recovery and found no receipt. Waited60 seconds, then recovered
read-only again: config exists, attempt directory and receipt do not, and no
actual attempt runner was found (the process collector matches only itself).
Source input is retained separately in NCE_L012_SUBMITTED.lean.txt. Outcome is
UNRESOLVED; conservatively counts one Lean slot. No resubmission or unchanged
compile rerun is authorized or performed. Continue independent modules only.

Own budget guard tightened: Lean usage is the union of terminal receipts and
ledger submissions, so L012's unresolved slot counts against60 even without
a terminal receipt. No limit increased; no host/shared launcher changed.

L013: the new count commit's multiline record syntax failed parsing, leaving
its derived proofs with recovery terms. Keep the fields on one record line.
The inactive-row proof now closes the small false-control branch directly.
No count specification/domain/source invariant changed; L013 is excluded.
The same layout fix was applied to the unlaunched key-fill module.

After L012's unresolved submission, isolated the already-audited read_byte
interface and shared actual carrier into NEW target NCE_OpeningRead. It has no
read-window recurrence. The remaining continuation target now imports that
smaller module; key-fill imports only the byte/carrier module it actually needs.
This is source/dependency isolation, not a resubmission of L012 or a claimed
recovery pass. The original submitted source remains immutable in evidence.
No old module, host launcher or shared workspace object is rewritten.

L016 (isolated continuation): an extra dsimp step reports no progress. Replace
the staged tuple rewrites with one targeted symbolic simplification using the
same byte cut, induction hypothesis and ofFn successor law. No statement/domain
changed and no concrete832-byte reduction is requested. L016 is excluded.

L017's targeted simplification normalized commutative address additions before
the specific byte-read law could match. Keep address normalization exclusively
in the final pure-image goal, after consuming read/continuation equations.
No native domain or statement changed; failed-module recovery axioms excluded.

L018: explicit tuple pattern lets remained unreduced under the targeted
rewrites. Replace them in the NEW opening continuation with explicit pair
projections after each bind. This is the identical read order and returned
carrier, with no changed domain/specification. No existing source changed.

L019: pair projection isolation worked; the sole remaining image goal differs
by0+x versusx. Add Nat.zero_add to the final small symbolic image rewrite.
No read, carrier, domain or proposition changed. L019 remains excluded.

Independent queue L021-L025 ran ONE admitted scope at a time. L022 sort and
L025 leaf pass. L021: close the known nil tuple by kernel reflexivity and remove
an arithmetic tactic after simp had closed the goal. L023: split the actual
batch condition consistently for address bounds; expose the inherited single
write at its selected/outside coordinates; finish the unchanged word function
by definitional equality. L024: rename the reserved binder `at` to cursorValue.
All three failed modules are excluded. No cut domain or property was weakened.

L026 padding passes. L027 key's only remaining issue is if True not reducing
under the selected-write rewrite; use ite_true explicitly. L028 row-store:
state the fixed32-byte length as Nat, use getElem!_pos at the actual inner
list, and reconstruct records by constructor congruence instead of dependent
equality elimination. L029 count-level: expose entry's zero cursors, type
its front/count projections directly, and rewrite the actual level result
rather than an unused let binder. Existing count bounds suffice for the next
spent inequality. These are own proof repairs; no native spec/domain changes.

L030 key-fill and L032 count-level pass. L031: give getElem!_pos its actual
inner byte list and coordinate explicitly; congruence already closed scalar/
frame goals from the context, so handle only remaining goals. No statement
or domain changed. The failed row-store module remains excluded.

L033 row-store passes. L034: constructor congruence already discharged the
named scalar frames; use only remaining goals. Expose the initialized cursor
projection before arithmetic and use Nat.zero_add in the final constructed
copy carrier. The source/index/window domains are unchanged; no native copy
pass is claimed, and the failed module is excluded.
