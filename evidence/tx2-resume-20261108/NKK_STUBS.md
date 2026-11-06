# NKK stubs and oracle domains

No field multiplication stub or field-product Kani proof. No kani function contract, stub_verified, function pointer or writable static.

| Stub/oracle | Domain | Paired law / status |
|---|---|---|
| exact KMX copy_nonoverlapping / copy_from_slice | supplied patch bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67 | KMX_CopyMeaning and KMX_ value laws retained; matched controls required per new cut |
| RawOracle::raw | full raw4/raw32 reply, arbitrary post cursor; immutable1768 backing | CLOSED NJZ_Readers.raw_cut at SAME arguments; source domain proof and native fold installation pending |

All new native code lives in own scratch, committed as evidence source/patch only. Frozen dependency graph and deployed feature closure are validated before every Kani run; CARGO_NET_OFFLINE=true; lock checked unchanged afterwards. Own CARGO_TARGET_DIR is recorded per receipt.
