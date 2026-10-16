Actual extracted terminal success to live parsePublic, Lean 4.32

ExtractedTerminalPublicBridge.terminal_serializer_parsePublic consumes:
- actual extracted terminal Withdrawal validation success on c,p;
- actual extracted semantic public_bytes success on Withdrawal(toSerializer p,t).
The fixed toSerializer composes the two checked all-nine-field maps. The theorem
produces live SemanticPublicWire.parsePublic on those exact output bytes and the
PublicSourceRaw.toWire equation for the fixed projected public. No separate
payment-helper or ASWP-encoder success premise is required: checked same-public
terminal, encoder, carrier and public bridges supply them.

terminal_serializer_supplied_public additionally states the exact fixed wire
projection and supplied = SemanticPublicWire.toPublic wire equality. This gives
the live hpub-shaped equation for that supplied public; it does not infer its
binding from terminal validation or from the independently supplied transition t.

The first joint import confirmed a generated payment-error discriminant instance
collision. A one-sided Terminal naming adapter expands only that fourteen-code
attribute to identical tags and a qualified instance. Its inverse recovers every
original emitted byte; all other attributes, original sources/caches and the
public serializer sources remain untouched. Original/adapted definition and all
fourteen constructor audits have byte-identical logs (4bb8112736d4e8c0ead02b0ebbc3c4605446fc0bc325ff3938c5c709cbc97e5c).

All eleven affected targets passed their first checks after this adapter. The
actual generated function audit and all requested proof reports are standard-only.
Final composition: 2.011 s, peak process RSS 3,849,600 KiB, sampled cgroup 733,945,856 B,
zero process/cgroup swap; both exported theorems use only propext, Classical.choice,
Quot.sound. Every target ran serially under 6 GiB high / 8 GiB max / swap 0. Fifty imported
project modules were initially verified from exact source/runtime/import/object
receipts; only the six affected Terminal modules were removed from that snapshot.
Caller carrier/public files were rechecked against the newer checked Caller Types.
No unchanged public/R17/backend closure replay occurred.

The bundle retains the failed joint import, original and adapted audits, exact
staged sources, receipts, runtime/import pins, namespace-link journals and final
object. All 134 member hashes and final source/object hashes were independently
verified locally. The original extraction mirrors remain separately pinned.

Open: establishing actual semantic serializer success in the runtime caller;
supplied-public equality; admitted verifier reachability; account and omitted
metadata binding beyond exposed terminal checks; extraction-tool correctness.
The checked result is a one-kernel composition of the extracted computations and
live Lean parser, not a full Rust execution or protocol source-refinement theorem.
