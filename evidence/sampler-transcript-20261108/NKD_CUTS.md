# NKD typed cuts and source association

Target not yet established. No ledger admission yet.

The native source is frozen4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. All cuts use one SAME invocation; independent gate replies are instantiated forward with the CLOSED source child, per(aq)(5). No inverse log equality, free operation dictionary or child endpoint premise is used.

| Row | Typed cut / G | Native packet | Frame and source consumer |
|---|---|---|---|
| TX1:157 decode8 | eight canonical U32 digits; G=NGT_NBL_DecodeNative.pack | NGT_K013/014 | NKD_Decode.root; full returned eight coordinates, no mutation |
| TX1:159 low_base_p_digits | NKD_Low.Cut=LowTrace: eight LPk_Induction.Digits, each Pass contains scalar relation plus ordered writeback | NGT_K015/016,021–036,037/038; LPk mathematical induction reused | NKD_Low.root; full digits and low quotient, canonicality and quotient<=256 |
| TX1:155 add_small_base_p | NKD_Add.Cut=NBA_AddCarry.Trace, eight source-ordered digit/carry transitions | NGT_K007/008,035/036,041/042 | NKD_Add.root; all eight mutated words and Bool, canonical output |
| TX1:160 ordinary_sample | low trace on SAME block, then canonical pack | NGT_K009/010 plus closed low/decode packets | NKD_Ordinary.root discharges both children |
| TX1:158 gamma_sample | NKD_Gamma.Cut=NGT_Reduction.Scalar block true out; ordinary constructor impossible at true; plain/wrapped contain ordered low/add traces and exact pack | NGT_K011/012 plus closed low/add/decode packets | NKD_Gamma.root; both carry branches; NGT_Reduction.second_carry proves reached debug check |
| TX1:165 absorb | NKD_Absorb.G: checked160+row then exact state32/tag2/length4/payload descriptors, digest reply returned as state | transcript native revalidation pending | total Result equality; only state replaced, hash retained |
| TX1:166 block | NKD_Block.G: absorb, read absorbed/[1], advance SAME absorbed/[2] | transcript native revalidation pending | total Result equality; absorb child discharged internally |
| TX1:167 new | NKD_New.G: deployed domain29, variant tag, semantic32, digest reply paired with SAME hash | transcript native revalidation pending | all three variants, total Result equality |

Canonical decode/add input is a caller obligation only for their direct public packets. Ordinary/gamma derive it internally from NKD_Low.root and NBL_AddNative.canonical. Gamma quotient+1<=257 is NGT_NBL_SamplerReplay.increment; second amount=1. No precondition stronger than those established by the actual sample callers is added. Long-division remainder<P starts at0 and each native scalar gate establishes the next remainder bound. No field multiplication occurs.

Low-level immutable std/casts/indexing/iterators execute in the cuts; Lean uses pinned Aeneas std and retained value laws, per(au). Scalar/copy frame laws and control/induction are separate from complete whole-function value claims. Runtime SHA value is the existing trust row; runtime input association is not inferred from a pointer alone.

Root inventory check (aq)(2): sampler inputs plus canonical/small domains and explicitly reviewed per-step cuts; transcript roots quantify the headline digest interpretation and source arguments, with no output, success or endpoint-equality hypothesis. Native-to-source interpretation and source-to-ELF retain P6/D188 option-A trust; reclassification, no premise removal. Per-deployed runtime instantiation remains to be compiled before any transcript closure.

## Source-generated deployed transcript cuts

NKD_make_native.py obtains each complete frozen Rust method from Git and permits ONLY: replace generic H with the actual program's SolanaDigest, add a LOCAL Log parameter, replace the digest child by observed_digest, and thread that log through block→absorb. Self is the value carrier {state32,hash:SolanaDigest}; no field is omitted. NKD_NATIVE_CORRESPONDENCE.json retains each original span and generated span/hash. NKD_harness.patch is the scratch-only overlay on the retained NGT source tree; NKD_NATIVE_SETUP.json pins the predecessor copy and frozen lock. This is the reviewed native cut/transcription of(ai)(5)/(y), not a new extraction, a new shipped implementation or a proof of SHA.

The fixed SolanaDigest is imported from the actual frozen program module. Its zero-sized hash carrier is retained by every cut; no generic/function-pointer backend is credited. observed_digest is the child oracle of(y)/(aq): arbitrary three LOCAL replies, exact call index, descriptor count/lengths, checked header bytes, live payload pointer+length, arbitrary state/reply byte coordinate, exact new domain byte coordinate, real Variant::tag, and unchanged reply return. All branches for the deployed constructor variants and row<=95,payload<=8192 are covered. Shared payload bytes are arbitrary, not zero-filled. Native K007/K002 (new), K003/K004 (absorb), K005/K006 (block) have identical paired source hashes and expected semantic controls; no SHA body is entered.

Forward instantiation(aq)(5): substitute the SAME runtime digest result at each source-ordered observed call. NKD_Absorb/Block/New.root equate G to the ACTUAL emitted cohort body on ALL Result arms. NKD_Runtime specializes that equality to the CLOSED runtime-forwarding interpretation, and NKD_TranscriptPackets constructs every absorbed/read/advance reply from hashv at the exact parts, with tag success DERIVED from row<=95. No reply/output/child-success premise remains. NKD_Domains proves every descriptor is inside the CLOSED NGC forwarding domain9parts, each<=57607, and reuses the complete shared-input frame law. Runtime SHA=H/returningValue is unchanged trust. Arbitrary observed oracle seeds are not equated wholesale to a callee poststate; only the returned32-byte reply is the digest child's footprint.

The original common sampler/opening-transcript unit domains and incoming parent provenance remain recorded, not deleted. Native payload coverage extends the prepare2048 domain to include query8192. New covers all S1/S2/D variants even though the deployed Prepared path selects S2. NKD_Values carries the SAME gamma output into canonicality and GammaRankMeaning. Nothing closes prepare087 or other caller rows automatically.
