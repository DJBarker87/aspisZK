# NBV copy and stub table

Exact KMX patch SHA256 `bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67`. Applied verbatim in NBV_src; KMX functions unchanged.

No field arithmetic is reached or stubbed. The field-stub/emitted-ok theorem requirement is therefore N/A. Digest callback returns are arbitrary runtime replies; their VALUE stays the existing SHA/H realization item.

| Cut | Positive | Matched negative | Status |
|---|---|---|---|
| K048/K050 prefix | K003: pass | K002: expected-negative-fail | RESTORED LOCAL CUT |
| Admitted complete copy candidate | K009: pass | K015: expected-negative-fail | RESTORED LOCAL CUT |
| Parent reply32 | K004: pass | K014: expected-negative-fail | RESTORED LOCAL CUT |
| Full selected store frame | K007: pass | K008: expected-negative-fail | RESTORED LOCAL CUT |
| Leaf grammar/reply | K016: pass | K017: expected-negative-fail | RESTORED LOCAL CUT |
| Key write/frame | K018: pass | K019: expected-negative-fail | RESTORED LOCAL CUT |
| Sort step/frame | K020: pass | K021: expected-negative-fail | RESTORED LOCAL CUT |
| Combined leaf/new row | K028: timeout | K029: expected-negative-fail | NO CREDIT |
| Post-hash decision | K030: pass | K031: expected-negative-fail | RESTORED LOCAL CUT |
| Post-hash new | K032: pass | K033: expected-negative-fail | RESTORED LOCAL CUT |
| Post-hash equal | K034: pass | K035: expected-negative-fail | RESTORED LOCAL CUT |
| Post-hash unequal | K036: pass | K037: expected-negative-fail | RESTORED LOCAL CUT |
| Three roots | K040: pass | K041: expected-negative-fail | RESTORED LOCAL CUT |
| Installed opening window | K042: timeout | K043: timeout | NO CREDIT |
| Paired row window | K044: pass | K045: expected-negative-fail | RESTORED LOCAL CUT |
| Supplied row window | K046: pass | K047: expected-negative-fail | RESTORED LOCAL CUT |
| Short row window | K048: pass | K049: expected-negative-fail | RESTORED LOCAL CUT |
| Padding8 conversion | K026: pass | K050: expected-negative-fail | RESTORED LOCAL CUT |

K005/K006 use the same32-byte reply mechanism and KMX configuration as K004/K014; their full-scratch pointer/selected-byte positive checks pass. This does not close a full row carrier or verifier unit. All inherited copy-dependent cuts not explicitly restored above remain suspended and are not used as full-unit credit.

Activated replacements: KMX_copy_from_slice, KMX_copy_nonoverlapping, KMX_clone_from_slice, with generic entry stubbing across reached Copy monomorphizations (u8/u32/u64/byte arrays). No Vec growth/append/realloc is reached by the credited cuts. Preconditions are matching lengths, valid/aligned/nonoverlapping regions and T:Copy; native array/slice bounds and memory checks are checked in each harness.

Lean meanings reused: KMX_CopyMeaning.loop_spec/copy_prefix/copy_frame. NBV_CopyComposition.window_value/opening_frame/adjacent_windows apply them; NBV_CountInitialization constructs the live initialized count carrier. The original KMX native differential / paired controls / standard-axioms audit are imported read-only, not rerun or claimed as universal Rust-to-Lean equivalence.
