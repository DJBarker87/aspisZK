# Powers-return harness alignment correction

The raw byte-array return abstraction cast a pointer whose static source
alignment was1 to an E-array reference. Do not rely on incidental stack
alignment. The replacement first uses by-value transmute to a typed [E;29],
then casts only between typed E arrays under its asserted N=29 domain. It
still represents every928-bit-pattern byte sequence (928 bytes, not928 bits).
No field value equation or canonicality assumption was added.

K018 is superseded pending the focused scratch-write rerun. K004 terminates
at queries; K017 terminates inside powers before return construction; K019
checks the post-write call cut with no powers replacement. Their credited
reachable paths do not execute the changed pointer transfer. Record-only,
transcript and query-core gates do not use this return abstraction.
This is a harness validity correction, not a frozen Rust source finding.
