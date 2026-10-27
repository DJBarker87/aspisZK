# SDK child worker handoff

**Incomplete: target not yet established.** Branch
`codex/cx-sdk-child-20261025`. No push. Budget used58/100 Lean and0/40 Kani;
the budget is NOT exhausted. No checked shipped-source counterexample.

`SdkC_BatchPair.accepted_pair` derives both complete source-computed batch
logs from one actual accepted wrapper pair, under existing D188/P1/success-only
RuntimeSyscall and std boundaries. `same_pair` applies to the exact f/s cuts
already exported by Op5T_Final, so integration need not choose another pair.
Both installed source bodies have all-input erasure proofs, and their own
read logs cannot contain a fabricated reply. No erased child/log/batch-success
parameter is used to derive those logs.

Both indexed authentication helpers now use partial native syscalls; only
the IDEAL instance is total. Wire/query/root provenance remains explicit.
`SdkC_Replay.recover_or_collision` obtains all22 indexed openings from the
original first-commitment prefix without assuming the canonical reads were
already in the native log. Replay costs at most1040 additional oracle calls;
its collision loss is explicitly6*(Q+1040)^2/256^32. It preserves the original
commitment cut. This is a generic source+replay experiment result, not an
instantiated frozen native security experiment.

Remaining required deliverable: **SdkC_Accepted**, preserving ALL Op5T_Final
conclusions with the entire arbitrary SDK child/marks replaced by concrete
source instrumentation on the same pair. It has NOT been supplied. Remaining
source/hash callbacks cannot simply be assigned empty logs or wrapped in a
new source-equality hypothesis. The actual global source experiment/budget
and Session A prepared/query/root/frame provenance also remain to instantiate.
No full SDK accepted-pair non-vacuity witness was proved; the checked fixture
is an installed leaf only. By the owner's completion rule this is NOT closure
of the assigned top-premise row. See SdkC_premise-audit.json and exact
before/checked-after statements for the narrower theorem's quantifiers.

Evidence: stages0–4;58 complete command/source/deps/exit/wall/RSS/swap/cgroup/
axioms receipts. Final focused audit025 is green for all55 new named theorems,
standard axioms only. All successful modules have focused compilation;
no package/full release replay. Peak RSS5189432KiB,swap0; caps unchanged.
Source/object pins and static checks retained. No shipped source or cfg(kani)
change, hence no ELF rebuild trigger. Full inherited pins are in
SdkC_shipped_pins.json. No keys, session A worktree or other-worker prefixes
touched. All commits are local.
