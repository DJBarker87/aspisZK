# NHK substitutions and domains

Exact prescribed KMX_copy_stubs.patch:
`bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67`.
Installed KMX_stubs.rs, KMX_native.rs and KMX_CopyMeaning.lean are checked
against the inherited exact hashes before every native launch. The only
copy stub is core::ptr::copy_nonoverlapping ->
crate::KMX_stubs::KMX_copy_nonoverlapping. Each credited copy-dependent shape
needs a matched assertion failure in the identical configuration. No private
copy implementation, writable static, function-pointer observer or field
multiplication is introduced.

| Boundary | Paired model law / domain | Status |
|---|---|---|
| Retained NHB membership contracts | NHB_Membership.reference_eq / prefix_membership; exact length, canonical18-bit and inactive-zero conditions where stated | Only historical complete pairs credited; NHB_K057 alone is excluded |
| NHK per-length native contains | Same laws; same22-cell prestate, x18, inactive-zero and literal required length | Per-attempt table; timeout never used as stub |
| Native prefix/suffix split | NHK_WindowLaws.native_split; both windows on the SAME list, cut<=length | Unchecked until native split plus both child laws pass |
| NHB opaque membership reply | NHB_K053/054 records SAME candidate, active prefix, post-increment draws and one call | Conditional until the precise length's native value law is available |
| NGQ scan reply | NGQ_K046/047; NHB_BlockTrace.walk_source and NHB_OuterState.association | Unconstrained full scan reply and Bool; exact before/after/carry/log frame; child law still required |
| NGQ digest replies | NGQ_MaterializeChain.normalized/run; NHK_EventChain.pair_trace/producer | Native byte slices/replies only; value=H stays approved runtime realization trust |

New membership gates reach no verifier code: they compile frozen aspis-core/r0
and retain the resolved frozen graph. No new stub_verified interface family is
introduced. The admitted historical Bool contracts and their matched controls
are reused; no non-Arbitrary carrier is passed through stub_verified.
No field multiplication stub exists, so there is no new field law to add to
LPh_STUBS.md. Tool semantic transport, std/allocator/ABI/compiler/Aeneas and
runtime realization trust is retained, not removed.

## Final discharge table

The native membership table now covers0..21 with no missing case. The old
full/split/arbitrary-offset timeouts retain zero credit. New fixed-prefix
checks execute full native contains, not a mathematical membership stub.

NHK_member_logged in K034/035 returns the supplied arbitrary Bool, records
exact candidate/prefix length/post-increment draws/prestate window and writes
only the local log. The paired Lean law is NHK_WordAssociation.substitute
with NHB_Membership.prefix_membership; native child value is supplied by the
complete NHK_MEMBERSHIP_CALLEES table. Domain: len<22/draws<64 at membership,
same canonical/inactive source prestate for16/18/19, masked candidate; all
other length certificates cover all raw u32 inputs. Caller invariants come
from NativeWords.domain_preserved, NHB_Canonical/NHB_Inactive and decode cuts.
No stub lacking a child law is used. NHK_WordReference.correspondence pairs
the explicit native G contract with the reviewed safe reference. Bool plus
local record effects is the admitted interface; no new stub_verified family
requires ruling(t) calibration. All35 inherited selected pairs revalidate
without replay (NHK_REVALIDATED_REUSE.json).
