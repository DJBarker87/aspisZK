# NMK stub inventory

No field multiplication is proved in Kani and no new field-operation stub is introduced. No function contracts or stub_verified are used by these experiments. No writable static or observer/function-pointer value assertion occurs. The generic child signature is retained.

| Cut | Closed theorem / packet | Domain and status |
|---|---|---|
| NMK_parse_cut | NLE_ParseInstall.emitted; NJS_Parse.source; Op3I_ParseLaws source parser law | all proof slices; in these original-length branches57607; exact16 header bytes tested |
| NMK_marker_cut | NHV_ReleaseOps.mark; NMD actual marker K078–K082 | deployed literalNone/Parsed; own phase asserted, None from frozen parent call source; no pointer-value assertion |
| NMK_common_cut | NLT_CompleteRoot.root, ledger24 CLOSED | own proof57607/public<=1880/Root0 assertions; Root0 pairing NMK_RootWindow.root0_iff/pointwise. **Full result/records/physical/stop law missing; this is not an installed spec cut.** |
| KMX_copy_nonoverlapping | exact KMX_copy_stubs.patch | sha256bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67; source hashes checked every run; matching copy-negative must FAIL |

NMK_Hash digest is an existing-argument local-record channel for the experiment, not a runtime SHA implementation. Its four-cell write coverage is local only. No internal allocator/ABI record is silently identified with those cells. Partial backend/runtime abort handling remains absent from the Rust carrier and present explicitly in the Lean fold. No CLOSED065 credit is lost; it has simply not yet been transported to this parent certificate.
