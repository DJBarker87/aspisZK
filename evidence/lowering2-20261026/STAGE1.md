# Source identity census and recorded bridge

Low2_check_source_pins.py scans all fifteen named packet roots (including
Tx2N and T2Nat separately), all their JSON and recursively referenced repository
JSON. It compares 2,800 whole release-source pin references across 2,102 evidence
JSON files: 2,786 exact matches, 14 bridged references. These represent 479
unique (path, hash) pins on 478 files. No unbridged mismatch was found.
240 additional verification-kit/reference source pins have retained exact-byte
files; these are explicitly NOT claimed as release compilation units.

The sole bridge is the recorded S2W require_zero delta. The checker verifies
both old/new complete-file and function-body hashes, replaces exactly the
named old body and obtains the current file byte for byte, verifies the
existing S4 extraction/SDK source-pin checker and the accepted proof packet's
four Lean source hashes, then verifies a successful receipt for the exact
all_input_source_equivalence source and its standard-axioms audit line.
No historical extraction receipt is relabelled and no new trust item is added.
No Lean invocation was needed: the existing accepted S4 proof is reused.

Low2_source_pin_receipt.json records command, source revision, checker hash,
dependency fingerprint, exit, wall, RSS, swaps and axioms status. The census
alone does not close L186. Compiler membership, three pinned ELF hashes and
the retained S10 check remain separate gates. Source revision in the input
manifest includes only evidence changes since the initial source revision;
crates/ and programs/ are unchanged.
