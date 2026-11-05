# Actual canonical-window producer

Frozen candidate.rs canonical_scan checks round0[7527..7751] with echeck(false),
and then ONE contiguous echeck(false) on proof[7783..10055]. The latter is71
32-byte words:7 round1 words followed by64 final words. The folded-root bytes
7751..7783 are excluded from those field decoders. NIL_WindowLayout gives the
exact source-to-View per-word identities; it adds no canonical-window premise.

The CLOSED slice-S scanner checks the encoded reply/header and borrowed bytes;
the CLOSED slice-Q packets consume caller-established canonical fields. Neither
alone supplies canonical_scan's field-decoder reply. The actual TX1:084 call,
its complete echeck/loop interpretation, and the saved-proof/history identity
must be composed before these identities imply canonical7/7/64 at the tail.
TX1:084 is outside the direct TX2::tx2_common call closure. It remains an explicit
slice-boundary producer, as already recorded by NID; no fake scan success,
canonical-window assumption, digest-only inference or SameExecution is installed.

Read-only committed NIH status supplies decoder caller-domain progress, not a
CLOSED canonical_scan producer. All existing S/Q and NGV/NGO credit is retained
on its actual scope. Full tail hypothesis remains OPEN.
