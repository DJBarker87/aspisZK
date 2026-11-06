# NKA stub table

No field multiplication or arithmetic stub; no stub_verified or new contract shape. No writable static, Option<fn>/function-pointer-dependent Kani property, extraction, syscall-value model or new runtime row.

| Stub/observation | Paired law and domain |
|---|---|
| core::ptr::copy_nonoverlapping → exact KMX_copy_nonoverlapping | Existing KMX_CopyMeaning.loop_spec/copy_prefix/copy_frame/realloc_prefix; initialized Copy source (or valid MaybeUninit carrier), aligned valid disjoint ranges, in-bounds count. Exact patch SHA256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. No custom copy stub. Source and configuration pins: NKA_KMX_CONFIGURATION.json; matched original-name failures in campaign. |
| outer-step scan oracle | LOCAL Log, full22cell+len+draws havoc, SAME arguments and count. NKA_OuterCut.Cut is exact asserted pre/post; NJT_QScan/NJT_QDomains instantiate the066/067 children at SAME arguments. This is(y)/(ai)/(aq)(5) composition, not a std-operation oracle. |
| row/Box native observations at root | Exact retained NJG/NJM/NJT assertion/control projections, domains in CUTS and HYPOTHESIS_INVENTORY. Complete initialized-prefix and owned-carrier laws are derived, no endpoint hypothesis. |

Safe std uses pinned Aeneas/P7 and native Kani Vec/Box per(au). Unsafe set_len/cast/assume_init uses the P6 native window packet. The named allocator action and quantified r are installed at the source reserve site, not assumed successful. RuntimeCpiReadonlyEntry7 is unused. P6/D188 option-A semantic transport is RECLASSIFICATION; no trust row added/removed/widened.

The typed-write observation has a fresh LOCAL completed flag after the literal typed store (K029/K030); NKA_InitHistory derives Ready on the identical Storage passed to BoxCut. K031/K032 use a real local Allocator implementation as a test instance of std reserve failure, not a stub/replacement of Global or a new allocator trust row. No field arithmetic law or contract shape was added.
