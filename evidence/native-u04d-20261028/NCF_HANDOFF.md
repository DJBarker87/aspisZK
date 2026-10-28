# NCF U04 continuation handoff

S2 OPEN; deployed 100-bit target not yet established. Branch
codex/cx-native-u04d-20261028. All fourteen whole slots remain OPEN.

## Established components

- op29/op30 actual native contracts on full typed entries/every u64 slot, their
  inverse postcondition controls and local stub_verified use/control pairs:
  K002–009. NCF_EntryContract.op29_exact/op30_exact match the cohort Bool
  predicate without changing NBX's candidates. These are local contracts and
  values, not whole SDK extraction components.
- Five decoder wrong-length pairs on symbolic valid lengths, zero-initialized
  backing with one arbitrary byte at arbitrary offset: K010–019. Exact domain
  and arbitrary-payload gap are in NCF_STAGE2_FINDINGS / NCF_PAYLOAD_FINDING.
- One selected mutable iterator row/write/frame: master K020/K021;
  checkpoint corrected K024/K025. K022/K023 excluded for an own wrong capacity
  constant. These selected nth fragments do not prove the original decoder's
  iterator prestate/next association or its full loop.
- Box component checks K030–045: arbitrary complete typed master/checkpoint,
  arbitrary initialized field/array coordinate, two runs on identical typed
  arguments, ambient coordinate preservation, distinct simultaneously live Box
  allocations, and surviving Box preservation after the other is dropped.
  Eight positive checks pass, eight inverse controls fail in exact KMX config.
  These do not replace native decoders or prove account/Box caller composition.

All NBX/NCC modules/evidence are reused; no old theorem is re-proved. New proofs
only: NCF_EntryContract, successful L003; standard axioms
propext/Classical.choice/Quot.sound. New source contains no sorry/axiom/admit or
native_decide/heartbeat/depth override. L002 failed elaboration (no credit),
L001 submitted transport unresolved (never resubmitted). The corrected L003
source differs from both predecessors. Exact receipts/pins retain each attempt.

## Open components and next steps

The bridge table is authoritative for each slot. No AeneasExtraction component,
headline input, cryptographic assumption, runtime trust item or security metric
is discharged/changed. The native actual authentication call-site association
is still open for all slots. Reached callee domains must be proved on the SAME
native caller execution; independent native getters or a model projection do
not establish that association. Intervening PDA/decoder/borrow/allocator calls
must use CLOSED bridges in their domains; no arbitrary successful replacement.

The arbitrary-payload allocation contract is unusable: K026 CAR-size failure;
K027 has both a postcondition and CAR failure; K028 is a mutable-slice
stub_verified compiler ICE. None is a valid control/pass. Unexecuted
arbitrary_long candidates have no credit. The one-window rejection domain is
reported explicitly, not silently promoted to every byte slice.

## Resources and freeze

One admitted capped scope at a time: MemoryHigh6G/MemoryMax8G/Swap0/Tasks64,
Lean -M7000, Rust opt-level3, 90s Kani solver gates. Complete frozen dependency
package+edge validation offline before each Kani run and unchanged lock after.
No --locked passed to cargo-kani. Exact KMX patch
bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67;
stub ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138.
No custom copy/field multiplication/SHA implementation stub. No timeout or
memory kill so far; no cap increase. Source snapshots and source-versioned
patches are retained. Formal/native section-6 fields are in NCF_ATTEMPTS.jsonl
and each receipt; printed failed-theorem placeholder axioms are excluded.

Repository crates/programs/Cargo.toml/lock are unchanged. Harnesses and
cfg-only annotations live solely in inherited owned host scratch, committed as
patches/receipts. No shipped change or SBF rebuild trigger. Inherited ELF pins,
not reproduced: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.

Cache retained: /home/dombarker/project-offloads/codex-cx-tx2codec-cache-20261028.
SInt2/library objects read-only; imported cache and 219 resolved Aeneas objects
pinned in L003-object-pins.json. No wallet/key action, other worktree/candidate
edit, binary/object/ELF commit, push or merge. Budget/final audit follows below.
