# Scope discipline incident

NBL_L016 was accidentally launched while NBL_K003 was active. The local
write_stdin poll returned an ongoing session; I incorrectly proceeded with
the Lean launch. Its capped scope completed in5.469367863seconds, exit1.
No running Lean process remained when the error was noticed; K003 alone
continued. No caps, host infrastructure, other job or key was changed.
The overlap violates the one-scope rule and is NOT reported as compliant.

Correction: both OWN runner scripts now use one shared atomic NBL_ACTIVE.json
creation before admission. Any active marker refuses a second launch. Removal
requires that the same attempt's terminal receipt has been recovered. A
preflight/transport failure leaves the marker in place for explicit diagnosis.
No shared launcher, reservation, shim, cache or monitor was modified.
