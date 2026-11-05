# Prefix producer packet

Native K023/K025 checks the complete frozen Prefix::parse control on every
length 0..57607 and 27 nonempty borrowed record windows, arbitrary child failure
position and all11 source WireError variants with full u8/usize payloads. The
child cut's successful output is the actual borrowed input window and checked
next offset; it cannot manufacture an independent Prefix. All27 call indices,
starts and widths are checked. Root pointer is unchanged. Successful terminal
length is13831; shorter/longer inputs retain exact source rejection.

NGX_PrefixSource.source is the full emitted retained parser Result equation,
not an accepted-run equation: primitive failure, divergence and all WireError
branches remain in the program. The five reused Rust bodies are byte identical
to frozen4bb3b3f5 modulo comments/whitespace; pins and the complete immutable
retained source are committed. Child parse_record_at is NGX CLOSED, in turn
using parse_record, NFU row_shape and validate_record_fields. No child success
is a premise: success is conditional on the native parser's actual checks.

NGX_PrefixGeometry proves the exact sparse starts/width recurrence, bounded
starts<=12898 and terminal13831. NGX_PrefixCarrier.producer_domain derives
start<=13000, 5<=width<=3717 and end<=17000 for every row0..26. These establish
the previously conditional getter/payload PacketDomains on the SAME producer
windows. The two nominal Prefix owners have exactly the same root32/records27;
roundtrips/fields/full_result preserve both values and every error payload.

No digest or protocol query occurs in this parser. Query order is therefore
empty, rather than inferred from result erasure. Native copy sites use the exact
KMX patch and same-name failing control. No field products or fn pointers.

ADMITTED by L064/L065/L066 and NGX_stage3_validate.py. This file alone
never promotes row138; see NGX_CLOSED.json and NGX_LEDGER_DELTA.json.
