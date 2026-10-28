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
