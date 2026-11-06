# Native support, not TX1:136 closure

All NLI_K runs use the scratch source only, optimized cargo-kani0.67.0, CARGO_NET_OFFLINE=true, frozen lock/complete resolved-graph validation before each run and unchanged-lock validation after it. Per-run receipts pin the source, actual deployed SolanaDigest, features, graph, lock, scope and target directory. The actual verifier source is unchanged. A returned local oracle is not a successful-child hypothesis: both Ok and every modeled Error are covered; outer aborts enter no return suffix. There are no new field stubs, multiplications, digest-value implementations, function contracts or stub_verified uses.

Exact copy mitigation: NLI_KMX.patch SHA256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. No alternative copy stub. The KMX include is in the library; program harnesses instantiate the actual private program SolanaDigest. Copy-dependent credit is limited to a window with its matching failing control. K021's constructor probe has no matched control and earns NO credit. The old Hash(u64) constructor windows are not credited as deployed runs.

| Window | Positive / matched control | Exact scope |
|---|---|---|
| rounds input | K004 / K005 | One entered call, SAME27 descriptor views of original13831-byte backing, root byte, original transcript state/next and arbitrary readonly backing byte. Does not infer payload from address. |
| rounds running | K006 / K007 | Complete Result tag/error and running value. |
| rounds alpha | K008 / K009 | Complete Result tag/error and one arbitrary alpha cell. |
| rounds transcript | K010 / K011 | Complete Result tag/error and arbitrary returned state byte plus next. |
| rounds None stability | K012 / K013 | Same input shape under renamed family, same verdicts; only narrow ruling(al) scope. K-2 quarantine otherwise unchanged. |
| claims payload | K015 / K016 | Post-callee Result, arbitrary cell of the full3x29 owned Box, same payload. |
| claims owner | K017 / K018 | Post-callee Result and same nonempty1392-byte Box owner. |
| claims entry | K019 / K020 | Original prefix root/selected record descriptor/readonly backing byte, before child entry/abort. |
| low callback | K022 / K023 | ONE i<16 iteration, arbitrary initialized/uninitialized pre-cell; writes claims[0][i] and preserves arbitrary source claims cell. |
| high callback | K024 PASS / K025 TIMEOUT | NO native credit: positive window passed but matching negative control timed out. Requires a substantively split new shape in a future budget, never unchanged rerun. |

K003 timed out on whole-buffer symbolic data indexing; K004 removes that mux and uses descriptor plus pointwise-frame/realization composition. K014 timed out on the compound full-wire/owned-return claims shape; entry and return scopes are split. Neither timed-out shape was rerun unchanged or given more time/memory. K001 codegen placement failure was repaired before proofs. K002 codegen-only is no proof credit.

Lean support: NLI_RoundsWindows.complete performs ONE-return field extensionality; NLI_RoundsCarry/source and NLI_RoundsInstall/source carry CLOSED134 at SAME parsed prefix and transcript with internally derived hash frame. NLI_ViewFrames transports original backing-byte realization by the arbitrary readonly frame. NLI_FromFn.write_prefix/fill_prefix and byte_frame provide partial-initialization induction and exact KMX disjoint frame; NLI_CallbackAssociation relates source closures on SAME Claims. These require final successful compile/audit receipts. They do not by themselves install the physical parent slots, nested occurrence order, stack initialization, or allocator/lifecycle interpretation. Those remain in NLI_REMAINING.md.
