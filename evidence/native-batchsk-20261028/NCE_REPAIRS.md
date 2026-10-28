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
