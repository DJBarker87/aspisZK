# Two local U03 validators — CLOSED

This closes exactly `pair_terminal::validate_verified_afterstate` and `pair_tree_profile::validate_pool_v1_pair_live_snapshot_v1` from frozen Rust4bb3b3f51e16b4525f1d10336e2b0bcbbd775387 to the adopted `AspisR1TerminalDecoder.Funs` definitions, under the retained native P6/TrustedStd carrier interpretation. U03 as a unit remains OPEN. No headline premise is removed; the deployed 100-bit target is not established.

## Claim and domain

Every typed native record, including every raw noncanonical M31 limb. Afterstate: arbitrary u64 next index, eight-u32 root and20 eight-u32 frontier rows. Live: arbitrary pool/domain32 bytes, sequence/index u64, root and20 rows. No successful validation, canonicality, independently selected child result, fixture or caller output is assumed. The native and cohort results have the SAME success/error tag and value; no panic is possible in the indexed loops under the proved invariant. Validators have no output mutation.

Carrier interpretation is fieldwise and preserves every field: native M31.0 to cohort U32.val, each ordered eight-limb Digest to Array U32 8#usize, twenty ordered frontier rows to Array Digest 20#usize, u64 to U64 and each32-byte array to Array U8 32#usize. No normalization/modulus is applied to raw limbs. The constructors used in the gates mechanically read the frozen struct fields; unused fields are arbitrary rather than zeroed.

- `NBH_Validators.afterstate` (L007): index0 or index>1048576 rejects InvalidAfterstateIndex FIRST; then noncanonical root or frontier rejects NonCanonicalAfterstate; otherwise Ok(). Capacity1048576 is accepted.
- `NBH_LiveValidator.source` (L015): zero pool/domain; sequence!=index; index>=1048576; noncanonical root/frontier, in that order. Each returns its exact source error. Capacity1048576 is rejected.

## Native/Lean composition

1. The CLOSED digest child is NBD_DIGEST_BRIDGE.md: NBD_K006, NBD_DigestNativeStep.source/compose, NBD_DigestTrace.native_result. `NBD_DigestInduction.source` gives the exact all-raw-limb natural bound and `same_scanner` the account variant. NBH_digest is constrained to precisely that value on EVERY input (NBH_STUBS.md). No stronger domain is imposed.
2. K004/K005 prove the two frozen native prefixes on arbitrary full records. A None result is a pending frontier, not a fabricated successful validator. Frozen index/binding/digest branch order is retained in NBH_NATIVE_PROBES.json.
3. K002/K003 prove ONE native frontier iteration at arbitrary prelevel<=20 and arbitrary frontier. The source while becomes one if and each early return exposes (level,Some(error)); success fallthrough exposes (nextLevel,None). The original prelevel distinguishes terminal level20 from an advancing iteration; each nonterminal success advances exactly one. There is no whole-frontier native replay. Level0 initialization and the bound/strict decrease are proved in the Lean loop induction (L004/L005).
4. `NBH_NativeFrontier.source` (L016) and `NBH_NativeLiveFrontier.source` (L017) associate those exact native observable pairs with each adopted loop body on the SAME prestate.
5. `NBH_Frontier.afterstate_loop` and `NBH_LiveFrontier.live_loop` prove the complete early-rejecting loop by a decreasing20-level measure. `NBH_FrontierTrace.good/result/afterstate/live/total` (L018) reuse NBD_DigestTrace's already-proved generic native-step induction at length20, associate each row's all-raw-limb predicate, and give total traces and the SAME full model Result. No new unproved execution law is inserted.
6. `NBH_ArrayEq.source` (L014) discharges both live binding-array comparisons symbolically on arbitrary arrays, without reducing concrete32-byte data. L007/L015 then compose the prefix and suffix into the complete validator results above.

No lower U00–U02 codec bridge is needed by these validators. No multiplication, SHA, whole-buffer Kani loop, XRn_Join kit or field stub occurs. All listed Lean results have only propext/Classical.choice/Quot.sound. Exact commands/revisions/hashes/dependency fingerprints/cgroup/exit/wall/RSS/swap/axioms are in each attempt receipt. K001 was a probe-path compilation rejection, superseded by changed K002; rejected drafts carry no closure credit.
