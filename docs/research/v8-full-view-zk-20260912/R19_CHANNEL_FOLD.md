# R19 working evidence and boundary

Date: 2026-09-21. Research only; not a deployment or full-security release.

## Source reconciliation

The supplied packet names `77fb78727c8b880b7c029828ad93083ff854f7f6`.
On intake, both the local and remote R18 branch pointed to
`c44188bf8ad96d8cf6acb87be33b5af467b17eca`; the older Git object was not
available locally. All ten supplied Git **blob** pins matched this base, and
all 26 packet payload size/hash checks passed. This is content reconciliation,
not a claim that the requested commit object was checked out. Existing work
was preserved on a separate `research/v8-r19-channel-fold-20260921` branch.

## Measured artifacts

These are complete primary executions at the diagnostic 100M cap, not supported
transaction-budget successes. Every row below still exhausts 1.2M and 1.4M.

| Artifact | World 0 CU | World 1 CU | Proof/profile |
|---|---:|---:|---|
| R18 starting primary (prior evidence) | 4,781,147 | 4,784,274 | Original R18 |
| R19 opening-b | 3,906,502 | 3,908,034 | Same R18 proof bytes |
| R19 factored-a, including opening-b | 3,877,513 | 3,879,042 | Same R18 proof bytes |
| R19 queries-a, including opening-b | 3,809,794 | 3,811,297 | Same R18 proof bytes |
| R19 combined-a: opening + queries + factored T163 | 3,780,805 | 3,782,305 | Same R18 proof bytes |
| R19 channel-c | 3,304,133 | 3,305,430 | New 699-field profile |
| R19 canonical-a | 3,279,621 | 3,280,813 | Same channel-c proof bytes |

Numbers consistently use the probe's JSON `cu` total, including its 56-CU
overhead, rather than the smaller program-log consumption. Canonical-a is the
guarded one-fold M31 multiplication experiment: it takes the narrow path only
when both u32 operands are below P, otherwise executing the original full-u64
reducer. The reducer, four-product accumulators and overflow checks stay intact.
Its actual Rust checker passes 200,098 product cases against the old reducer
and an independent u128 modulus, retaining the `2^62-1` negative control.
This saves 24,512 / 24,617 CU against channel-c, not hundreds of thousands.
Canonical-a ELF SHA-256:
`7a8aebda609d17257e454a3d2ca968906eaed704267148c9063fcdc9e906b0ee`.
The selected same-profile combined-a ELF SHA-256 is
`54a7e4ad41b731f490e715008e2ae66d2ca2caaedde4c46b5dc6053c2d0dcc65`.

For clarity, the arithmetic bound is an inspected integer argument, not a new
Lean source-semantics theorem. For canonical operands, x <= (P-1)^2,
`x >> 31 <= P-3`, and `x & P <= P`; hence the first fold is at most 2P-3.
It is congruent to x modulo P, so one subtraction canonicalizes it without
overflow. The guard supplies the range at the actual call, rather than an
assumption about every constructor of the public M31 tuple type. The general
full-u64 path remains byte-for-byte unchanged.

Channel-c ELF SHA-256:
`4abf63437c45025868ef4f11d2b3a3ccef59b601969f550c6f2814ad8053cb52`.
Its profile is
`AV8/R19/sparseG-T163/quadratic-channel-fold/research-v1`.
The cached SVM driver's old `bad-g-final` label denotes a mutation inside the
**combined** Final256 for this profile; it is not a second G final array.
That control rejects with Custom(6), at 1,851,993 / 1,847,891 CU under the
diagnostic cap. At supported budgets it exhausts resources, which is not a
checked rejection. Both accounts remain unchanged.

The channel SBF build passed the source permutation/table and stack-frame gates.
Build exit 0, wall 39.23 s, peak process RSS 619,388 KiB, swaps 0. It ran on the
NUC through Tailscale in a scope with MemoryHigh=5 GiB, MemoryMax=7 GiB,
MemorySwapMax=0 and TasksMax=128. SVM scopes use 2/3 GiB, zero swap, TasksMax=64.
Per-process RSS is not represented as a sampled aggregate cgroup peak.

## Compiled and source-exercised results

`lean/AspisV8R19/ChannelFold.lean` contains the scalar quadratic/boundary and
weight identities, a finite dot-product identity, an arbitrary common-inverse
opening identity, and finite weighted-contraction linearity. The focused cached
Lean invocation passed; its receipt and axioms output are in `evidence/r19-lean`.
These are algebraic facts, **not** source extraction or random-oracle theorems.

The new literal source absorbs p0,p2 before beta, retains both original
interpolant subtractions, both roots, canonical packed decoding, paired
authentication and all mixed image coefficients. It serializes one Final256
and the two new coefficients. The independently dense host verifier accepts
both genuine source fixtures. A separate actual Rust compact-terminal checker
passes 48 full-QM31 cases against independent dense transport/chord/fold
calculations, including beta=0/1/-1 and arbitrary final vectors/image residuals.
It retains the G image scales tau^3 and tau^4 separately. Its 48 mixed-image
checks include tau=0/1/-1 and zero/one fold challenges.

For both actual generated prefixes, the existing C1 correction remains at
rank 108 per selected column, and the H1 joint system remains rank 540 over
562 equations. The new G correction has 626 equations and rank 602. Its affine
target is solved and every original equation is checked, rather than accepting
rank alone. Independent source encoding/decoding then checks that both sent
channel coefficients, all seven first-relation coefficients, and combined
Final256 are retained. It keeps the stronger separate R/G final-zero
constraints; this is a sufficient fixed-prefix screen, not a proof that these
are the minimal constraints of the new transcript.

World 1 was interrupted on the user's pause request. Its incomplete log is
retained. Resumption reused the compiled stage-specific binary and a fresh
fixture directory; neither compilation nor successful world 0 was repeated.
The wire-control gate additionally passes 3,283 cases: all 2,796 fixed-field
canonical limbs, both old R18 profiles, canonical-valued changes to both new
coefficients/all relation and final fields, and authentication/framing changes.
The zero-recipient and zero-change witness fixtures reject at semantic error4
before PCS. Their intentionally unconstructed PCS suffix is not represented as
a complete bad opening proof.

The generated summary still prints the inherited old maximum-body-size label;
the actual parser uses 40,314 and the generated body is 39,638 bytes. Do not
interpret the stale printed label as a wire specification.

## First remaining security propositions

1. **Source joint-image/privacy:** prove universal compatibility of the legal
   mask correction with the enlarged observation map including p0,p2 and its
   affine witness offset, or exhibit and account for a source-valid exception.
   The two fixed-prefix solves do not establish an adaptive whole-view
   simulator, posterior distribution, or retry/publication law.
   More precisely, for each admissible actual source prefix pi and same-public
   witness change, show that the C1/H1 correction retains p0 and that its
   resulting target t(pi) lies in the image of the legal G observation matrix
   B(pi). Equivalently every left-kernel vector of B(pi) must annihilate t(pi).
   The observed rank 602 leaves 24 compatibility equations in the 626-row
   system; the successful two executions verify those equations only at their
   own prefixes. A universal theorem (or a bounded, source-valid bad event)
   is the next proposition, before any claimed distribution-preserving
   simulator/compiler composition.
2. **Pre-beta extraction/soundness:** obtain a coherent quotient pair and its
   weights fixed before beta in the actual commitment/oracle experiment.
   Post-beta extraction of only the combined quotient is insufficient. Any
   list multiplicity and gamma dependence must enter the bound.
3. **Challenge law:** connect the degree-two error bound to the actual shared
   oracle, including prequeries, cache hits, rejection and adaptive choices;
   no new IID/hiding premise or grinding credit has been introduced.
4. **Resources:** reduce a complete checked execution to the supported budget.
   The fastest prototype is still about 2.34 times 1.4M.

## Retained failed and non-release attempts

- Opening-a's generic `cargo test` pulled in unrelated old test modules with
  an unresolved HOST_HASH reference; the focused standalone checker replaced
  that entry point. No old regression was deleted to obtain a passing result.
- Channel-a stopped at an ambiguous staging replacement anchor. Channel-b
  failed compilation on an inner documentation comment after concatenation.
  Channel-c is the first accepted source build; these are not CU regressions.
- The first factored adapter review caught a missing low-factor contribution
  in the pivot shortcut; the accepted gate uses the complete `entry(...,1023)`.
- The new image check initially constructed tau^6 where the actual second
  channel uses tau^4. Lead review corrected the **checker**, before its accepted
  run, to use separate linear/quadratic coefficients. The protocol formula
  was not changed to fit the check.
- Query-sharing's initial local build lacked a durable capped resource
  receipt, and an early remote scope invocation did not apply the intended
  caps. Neither is counted as release evidence. The bounded live-cap gate is
  retained separately. Channel-opening predecessor a/d logs are retained
  alongside the successful e result (entry-point/cfg/checker plumbing fixes).
- Two query evidence JSON files originally had a literal trailing `\\n` token.
  Local copies were normalized to valid JSON; their recorded field/source
  hashes are unchanged, and the historical hash of the remote raw metadata
  remains a hash of its original bytes, not the normalized local copy.
- Canonical-a was initially staged inside channel-c. The accepted remote
  stage is preserved; the stager now rejects descendant output paths for
  future runs. New clones exclude build outputs and key material. This did
  not change the frozen input source manifest or any production path.

At this checkpoint the same-profile best is combined-a and the new-profile
prototype is canonical-a. Both selected artifacts have completed whole-primary
diagnostic measurements on both genuine worlds, with checked negative controls.
The actual channel opening differential also passes 32 arbitrary authenticated
record sets across six beta choices, preserving every malformed-input case of
the opening-b corpus. No production paths, negative regressions, keys, or wallet
state were removed or changed. No R19 push or deployment is implied.

The first combined-a world-0 probe was accidentally given an older R17 fixture
and rejected at semantic error4. That log is retained as a mis-targeted run,
not as evidence of a cheap candidate verifier. The corrected probe used the
unchanged R18 minimal world-0 fixture and completed at the CU shown above.
