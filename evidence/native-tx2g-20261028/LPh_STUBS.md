# NBP stub obligations

The closed digest-encoder substitution, its exact Lean theorems and all-raw
caller domain are in NBP_STUBS.md. No field multiplication stub is introduced.

OPEN substitution: NBP_format_reply replaces std::fmt::format in K040.
K040 is a wrapper-forwarding gate ONLY: one supplied owned one-byte String is
passed by identical pointer/length to sol_log, exactly once, and the wrapper
returns InvalidInstructionData for all eight error tags. The stub deliberately
does not claim to format its Arguments. No Lean theorem pairs this stub to the
actual allocating formatter, so it is an OPEN lower obligation and supplies NO
full-error-bridge closure credit. K002–K017 independently prove actual Debug
and message writer bytes. Joining those facts through actual allocation,
string ownership and cleanup remains open. Runtime log realization retained.
