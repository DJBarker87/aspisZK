# Ordered transcript events

Frozen queries first absorbs [old state, [0,160+row], little-endian u32 payload
length, payload]. Then, unconditionally before decoding, it issues eight pairs:
[state_k,[1]] for block_k; [state_k,[2]] for advance_k; next state=advance_k.
Thus there are17 digest calls when all calls return, including absorb, even when the sampler
later rejects. Neither sorting nor deduplication of addresses is permitted.

The sampler reads at most64 little-endian masked18-bit words in block/word order.
A repeated candidate consumes a draw and is discarded; a fresh candidate appends
to the survivor list. The ordered22 output positions are survivors, not a sorted
set. The stop check is BEFORE each word; no check follows a block's last word.
Success exactly at a block end can therefore select the NEXT advance. The caller
has already computed all eight advances. On success it commits the selected
advance; on decoder rejection it retains its absorbed state. Local state advances
were not yet committed to self. The22 from_m31 arguments are evaluated only on
success, in position order; deployed trace::value is unit/no effects.

Rejection is possible:64 equal candidates leave one survivor and finish rejects.
NGQ_ScanLaws proves this stream shape by symbolic duplicate induction (L011). Rejected attempts remain in candidate-consumption evidence; all17
issued digest events remain. There is no ninth-block retry. An unsuccessful or
diverging syscall has an attempted chronological prefix including that call;
NGP_OracleTransport supplies the existing prefix/exact transport once the native
association is constructed. We do not assume syscall totality or erase suffixes.

No schedule mismatch has been established. Source inspection, model equality,
and native same-execution association are recorded as distinct evidence.
