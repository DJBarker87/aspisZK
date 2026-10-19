# Binary privacy layout

Branch: `codex/r1-privacy-layout-20261019`. Branch base: `f9016d0a2`; handover snapshot:
`2d7d47218` (unverified binary copies). No sources or evidence were on the
host for these copies; the sent log had no attempts 6000–6099. Verification
starts at 6000 in env J, through the capped launcher (7000 MB / 7 GiB,
MemorySwapMax=0). Per-attempt receipts: `attempts.jsonl`.

## Scope and implementation

The binary chain lives beside the unchanged eight-way chain in modules
suffixed `Bin`. The existing privacy game/coupling types depend on the
concrete position type throughout; this change retains their separate
namespaces rather than changing the established eight-way theorem API.
Node indices have 17 non-root levels; the root is separate. Nodes have two
children, tag 0x12, and the designated field is the right child. Ancestor
indices use division by 2^(level+1).

## Handover verification

Attempt 6000 independently checked the handover's smallest module,
`GamesR1PBin`: exit 0, standard axioms. The subsequent focused builds below verify the remaining modules and the
multiproof/read-budget additions.

## Boundaries

`CommitReadsR1`, `ReadBudgetR1`, the Rust simulator and the soundness tree
are outside this change. Byte/source refinement remains a named premise,
as in the existing privacy theorem. No claim of candidate simulator or
multiproof verifier source extraction follows from this layout proof.

## Read sets and counts

`GamesR1PBin.card_NodeIdx` counts 262,142 non-root nodes per tree using a
17-term level sum. `card_Pos1` counts 2,359,413 + E1 + E2 attempt reads.
`LayoutCountR1PBin` connects `n1` to `115 + McR1 + 2`; the two extra reads
are the binding records. At E1=90,112 and E2=8,192, n1=2,457,717.

`EventsR1PBin.ROpen` retains aggregate coverage and adds two batch lists,
per-batch Nodup, exact batch path-union coverage, and union of batch fibre
sets. `batchReadSet`, `mem_batchReadSet`, `batch_toFinset`, `batch_length`
state the read set and exact number of reads without evaluating a large
universe. `RComLog` maps this opening list to the actual addresses and
answers; duplicate nodes across batches are allowed. These are wire
refinement premises, as ROpen/RComLog were before this change.

## Transcript separation obstruction

Unconditional node disjointness against arbitrary `TranscriptR1.Rest` is
false: `addrWith (.absS 0) f r` is a 32-byte digest followed by `[0,0xa0]`
and arbitrary `r.framed 0`. Taking f=`[0x12] ++ 31 zero bytes`, the framed
message to be 31 zero bytes, left child all-zero, and right child
`[0xa0] ++ 31 zero bytes`, produces the same 65-byte binary node record.
`R1Wire.frame/payload/final` are unconstrained functions, so this also
prevents an unconditional theorem about all wires. Per the binding rule
for false statements, that unconditional item is stopped.

`LayoutTagR1PBin` instead proves separation for every other commitment
record class, retained eight-way nodes, and transcript records under the
named `TranscriptNodeLengths` premise (framed length !=31; payload/final
length !=27). Proving this premise from actual source encodings remains a
wire-refinement obligation. The existing privacy argument never assumed
unconditional cross-class disjointness; its designated-field freshness
proofs remain the route used by the binary root.

## Focused verification

Green through the new read-set layer: 6001 Games (final count), 6002 Layout,
6003 Layout2, 6004 Layout3, 6010 LayoutTag, 6011 LayoutCount,
6012–6013 Coupling, 6014 Events. Every new theorem has a `#print axioms`
audit; successful checks use only propext, Classical.choice, Quot.sound.
Failed attempts 6005–6009 were isolated tag-module elaboration/proof fixes:
missing namespace, opaque byte-array traversal, then a final normalisation
step. The replacement proves byte-array traversal length symbolically.
No cap failure, cap increase or unchanged-source retry occurred.

## Completed roots and final audit

All 19 binary modules have a matching green env-J compile, in dependency
order. `manifest.json` records current source and object hashes, object
sizes and import-object fingerprints. The read-only `audit.py` checked
local/host source agreement, dependency order and every theorem's full
axiom report. No binaries or objects are committed. `build.py` reproduces
one-module sends using only 6000–6099; unchanged inputs remain forbidden.

- 6020 `AgreeR1P2Bin`; 6021 `FinalR1PBin.realModel_R1P`.
- 6022 `PrivacyR1PBin.privacy_R1_games'`.
- 6023 `R1J.PrivacySamplerSpendBin.privacy_R1_games_spendSampler_bin`
  discharges the sampler-law premise with the extracted spend sampler.
- 6024 `LayoutObstructionR1PBin.binary_duplex_overlap` kernel-checks the
  counterexample above (no axioms).
- 6027 `PrivacyBoundR1PBin.binary_exhaustion_le` and
  `privacy_R1_games_binary_bound` prove the actual binary phase-indexed
  error <= 2^-109 + 2^-137 for N=8 and qmax<=2^64, under RCommitCount and
  E_s<=2 L_s, including the two binding reads. The exhaustion slot is
  bounded by 2^-229. This instantiates the unchanged
  `ReadBudgetR1.r1_games_error_le` via `binary_games_error_le`.

There were 20 successful compiles over attempts 6000–6027, eight failed
focused attempts, and two unchanged-input refusals. Peak RSS across the
attempts: 4,151,428 KiB; every successful attempt has zero swaps and only
standard axioms. 6019 failed solely because added audit commands dropped
apostrophes from two theorem names; 6020 repairs those audit commands.
6025–6026 isolated the final numeric corollary's cast/comparison issues;
6027 uses symbolic power monotonicity rather than normalizing 2^496.
No resource cap was raised, and no memory-pressure failure occurred.

The original eight-way sources are byte-identical to the branch base.
FinalR1P and PrivacyR1P were submitted with their current dependency
fingerprints: both were refused unchanged (request 6024, which the
launcher did not consume). The matching standing green logs, 5760 and
5547, were read and checked and are retained in `standing-eightway.jsonl`.
The binary-obstruction compile then legitimately consumed 6024.

## Parameterisation, shared workspace, remaining work

No existing module was parameterised or replaced. The 14 handover binary
modules duplicate the concrete eight-way game/layout/coupling chain under
separate namespaces; five added binary modules supply separation, counts,
the obstruction, sampler closure and the bounded root. The original
8-way API remains unchanged. General mass, ROM, transcript and algebraic
proofs are reused through the existing imports. The new byte-array length
lemma is generic, as are the read-set/list facts over arbitrary fibre sets.

No existing eight-way shared source or object was rewritten. New Bin
sources/objects were installed in the shared J workspace; their earlier
versions were snapshotted under `J/snapshots/r1-privacy-layout` before
replacement. Every needed binary dependent was subsequently compiled with
its new import-object fingerprint. Only hashes and sizes leave the host.

The unconditional transcript-disjointness item is false and stopped with
a proved counterexample. The valid conditional separation theorem is
`LayoutR1PBin.nodeBytes_ne_transcript`; establishing
`TranscriptNodeLengths` for actual source wire encodings remains open.
Actual candidate realizations of the named wire/commitment/causality
premises remain source-refinement work, as in the original theorem.
The candidate Rust simulator, format-adoption implementation and soundness
proof tree were not changed. No wallet/account keys were touched.
