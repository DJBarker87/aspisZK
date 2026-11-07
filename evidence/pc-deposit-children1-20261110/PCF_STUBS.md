# PCF stubs

No accepted PCF root and no field-multiplication stub. Account-check contracts execute their real children. Exact KMX patch SHA256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67 is applied to the scratch tree; copy-dependent credit additionally needs its matched failing control. No custom copy stub, writable-static oracle or Option<fn> credit is used.

POOL:199 final stub pairing (no multiplication, no hash/PDA value trust):
| Stub | SAME-argument Lean theorem | Domain |
|---|---|---|
| PCF_Lane::canonical_reply | PCF_ChildLaws.scanner and PCF_CanonicalWords.complete | Any eight raw U32 limbs; the native harness constructs these exact limbs, no canonical-input restriction. |
| PCF_Lane::first_reply | PCF_FirstStub.first_reply and low_byte | Same eight limbs. The native stub asserts canonical_reply at its entry and K009 discharges this from the actual caller branch. The Lean value law itself holds on all eight raw limbs. |
PCF_LaneModel.complete ties the exact E002 extracted scalar reference to PCC.laneReference including the entire state, ordered empty effects, Ok byte, and NonCanonicalDigest Err. PCF_WordBridge.word_value establishes unchanged limb values; no changed argument or callee predicate is assumed in the root.

Append partial base isolation: PCF_AppendNative::bytes stubs encode_digest_canonical; paired theorem PCF_DigestShape.encoder (via PCF_AppendEncoder.words and PCF_EncodeByte.at_word) returns ok with the exact accepted DigestBytes.bytes for EVERY eight raw U32 limbs. E_full reference is PCB_AppendFullRef; exact source word0..7/four LE bytes order is retained. No canonicality premise or multiplication stub. The base domain roots.is_empty() reaches no encoder call, so native base success would not give nonempty-loop credit.

Final leaf route: direct real-body K059–K066; no Result-producing callee is substituted by stub_verified. Future callers of364/365/199 must use(ak) explicit-constructor logging stubs with all reachable Err arms and exact modifies. No field multiplication stub is used anywhere in accepted PCF packets. Append encoder isolation remains uncredited because K054 timed out.
