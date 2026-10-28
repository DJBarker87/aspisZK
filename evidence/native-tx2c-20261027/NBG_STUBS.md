# NBG stub register

No field multiplication is evaluated or proved in Kani. No LPb passing stage is
reused as new closure credit; no cfg-if/libc drift exception is asserted.

| Stub | Paired theorem / retained item | Domain and what caller establishes |
|---|---|---|
| `NBG_runtime::runtime_hashv` for `solana_program::hash::hashv` | `NBC_ReleaseLeaves.digest_result`; `NBG_Runtime.digest_transition`; approved runtime syscall/digest realization | Hash value is arbitrary32-byte reply. Stub asserts identical outer-slice pointer and length, increments a call counter, returns that reply. K005 uses two ordered parts, each arbitrary length0..32 and arbitrary contents; it establishes the descriptor identity and exactly one call. Universal source wrapper association also uses the exact unbranched one-expression frozen body, not an extrapolation of bounded slice tests. Runtime hash state and hash VALUE remain trusted; SHA is never unwound. |

`NBG_Runtime.digest_transition` is a source-shaped state law. It does not
install a dictionary or itself establish a native bridge. Coherent SInt2 uses
op43/op44; no op48/op49 digest/error attribution is made.

| `field::NBG_runtime::NBG_product` for native `M31::mul` | `AspisR1.LPf_BaseMultiply.source`, compiled unchanged L010; auxiliary `product_bound`/`word_product` | ALL raw u32 operands, a stronger proved domain than canonical-only. Returns arbitrary u32 constrained to `(x*y)%2147483647` and `<P`. LPf source proves both constraints and ok return; full u32 product fits u64. The range caller establishes raw32 by type; no nonzero/canonical operand premise is assumed. Native one-iteration K028 does not execute or prove multiplication. `NBG_SquareLoop.square_n_result` reuses symbolic induction. |

The explicit `<P` assume in NBG_product is the already-proved output bound, not a stronger input contract. No field stub exists without its named emitted-ok theorem.

Planned final K032 log stub: `NBG_runtime::NBG_log` replaces only
`solana_program::log::sol_log`, checks full message length and an arbitrary
selected byte, and counts exactly one call. `NBG_Error.message/transition`
(L069) retains the source-shaped state transition and coherent error value.
This is runtime-log abstraction, not a field stub. It does NOT prove formatter
allocation/failure/cleanup or actual op44 caller installation; error remains
OPEN even if the normal-message gate passes. Runtime log semantics retained.
