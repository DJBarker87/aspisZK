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
