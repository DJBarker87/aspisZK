# NLK fold design and status

Target not yet established. No CLOSED candidate yet. Source and full frozen
revisions are inherited as stated in NLK_HANDOFF. Ledger baseline NLG 564/0/35.

One `NLK_ParentFold.State` carries the current NLF parent token ledger and caller
state. Its step and append laws reuse NLF_ProgramFold rather than duplicating
NHZ's independent pure-event algebra; NLF supplies acquire/deref/release tokens
and runtime cell identity directly, including duplicate-key aliases. The SAME
runtime admission is the only source of initial counters/cells/liveness.

`NLK_BorrowScope` is an intermediate callback packet, not a row root: its
callback must be replaced by a CLOSED child on precisely the dereferenced
payload. Returned Ok AND returned Err Drop the temporary guard. Outer fail/div
stop with the acquire/deref prefix and guard still live. No allocation or child
success premise is licensed by these support laws.

`NLK_LaneFold` composes the prior per-iteration cuts, SAME root, terminal guard
and inherited NKY allocation law at 720 bytes/alignment8, for an arbitrary
consumed Reservation. This is still local: native header-to-op50 invocation,
actual constructor carrier, input geometry and complete effects must be bound
before promoting217. L003's provisional728 draft is superseded by L004 and
K001's actual layout check (with K002 failing control).

`NLK_PdaAbi` lifts arbitrary byte-coordinate observations to complete ordered
seed/program equality and reuses NLA status conversion. The output is quantified
op38; no hash/curve/PDA-value law is claimed. K005..K010 cover the literal pinned
deployed SDK branch with only the syscall replaced by a local-record oracle.
No writable static, function-pointer dependence or contract substitution occurs.
Unsupported-status native abort and full source caller chains remain required.

TX2:234 must fold both registry versions, every readonly/decode/PDA/comparison
prefix and child domains. TX2:233 must instantiate216/217/218/234 at SAME
produced arguments; TX2:242 must instantiate233 and its CLOSED descendants,
including the Clock outcome/slot and original proof borrow. Intermediate support
with free callbacks or cut equalities is never reported as a row root.
