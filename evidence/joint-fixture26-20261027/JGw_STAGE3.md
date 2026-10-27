# Actual TX1 array and scalar calls

JGw_Values0..9.source prove the native op0 array builder call on each actual
JFo_Opening.value0..9. Each returned array is built from its four actual ordered
32-byte record decodes from opening[672:800]. Forty canonical decoders,320 word
reads and all selected real-byte windows are checked.

JGw_Scalars0..9 contain JGw_Slot00_0..09_3.source:1040 scalar read instances,
26 per slot, four per query, on the actual 608-byte dot prefix. Source and byte
hash manifests are JGw_QUERY_WINDOWS.json and JGw_SLOT_WINDOWS.json. The proof
generators both pass --check. Inherited decoders/builders/range algebra are reused.

Attempts012..031 all pass. New theorem #print axioms reports are standard-only.
Exact resource/source/dependency records and complete warnings are retained in
per-attempt receipts. 024's first admission output was too long for the local
tool display and JSON parsing stopped before any upload/scope; a fresh
admission was obtained,allowed:true/exit0,then the single compile ran. No host
launcher/infrastructure changed. No source/helper admission added.

The complete batch, same-preparation query/flush/writer suffix, accepted1 and
joint non-vacuity remain open. FJv top counts83T/3P/13G unchanged,zero removal.
Budget31/100 Lean,0/10 Kani. No shipped files/ELFs changed.
