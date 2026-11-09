# Open release gates

Source: research commit `07123926e88273271344977a3fdc26d1780cde14`; the authority is section 6 of [`SOUNDNESS-STATUS.md`](SOUNDNESS-STATUS.md), with the figures for extraction provenance taken from `evidence/ledger30-20261111/NNN_LEDGER.json.xz` (field `NNN_extraction_provenance`) and the run-7 audit [`TAS_G0_AUDIT.json`](TAS_G0_AUDIT.json) (field `release_blockers`).

The release target is 100-bit classical soundness per attempt for the actual frozen R1 spend path, with no proof-of-work or grinding credit, and it is not yet established. The first four gates of the status document, which ask for every row to be closed, for every slot of the top-level statement to be filled by a proved term, for the two top theorems to compile with standard axioms only, and for their printed statements to be audited, have all been met; what follows are the gates that remain, each with what would close it.

## Extraction provenance

The 599 verified statements are proved about Lean definitions that the Charon and Aeneas tools produced from the frozen Rust, and a release claim needs a receipt showing that each such definition really is what those tools produce from that source. An audit found 336 generated Lean files without such a receipt; 18 were reproduced exactly from archived input, 317 could not be reproduced, and 2 differ semantically outside the domain the proofs use. None of this is a counterexample and no statement was reopened, but by a conservative name-matching count 578 of the 599 rows reach at least one unreproduced file. Later work found that fresh translations differ from the historical ones in their arithmetic because the historical translations were run with overflow checks on; the status document's reading is that re-running the tools with that recorded configuration restores provenance, and that campaign is under way. The gate closes when every generated definition reached by a credited proof is either reproduced from an archived input with the pinned tools, or re-generated and proved equal, definition by definition, to the committed one; any definition left without such an equality keeps its rows conditional.

## Cold replay of the final closure

The two top theorems were compiled in one combined import against cached objects, and a scan of the whole closure of 20,019 modules found it coherent, but that is not the same as rebuilding everything from source. The gate closes with one coherent cold replay of the final dependency closure in the pinned workspace, under capped resources, recording the target, exit status, wall time, peak memory, swap, source revision and the printed axioms.

## Source-to-binary audit

The proofs are about the frozen Rust source, and the native cross-checks were run on that source as compiled for the Kani model checker, not on the deployed ELF. The deployed ELF has been rebuilt bit for bit from the same source with the pinned recipe ([`BUILD.md`](BUILD.md)), and it has been tied to the live devnet program ([`DEVNET-RUN.md`](DEVNET-RUN.md)); what remains is the final trust and axiom audit of the closure together with the association between the source and the release ELFs (`f8c0ec72…43d4` and `63ad3e9c…4299`), including the allocator and ABI realisation row. Compiler semantic preservation stays a named trust row whatever this audit finds.

## Checked versus wrapping arithmetic

The Lean translations behind the verified statements were made with overflow checks on, so every integer operation in them either gives the true result or an error; the deployed program is built with Cargo's plain release profile, so its arithmetic wraps. The theorems therefore describe the checked program, and transferring them to the binary needs, on every reached path, either a proof that no checked operation can fail (so the two agree) or a proof that wrapping acceptance implies checked acceptance with the same result. The general lemma is proved, and of the arithmetic cones audited so far 35 are total, 63 are total only under a precondition their callers still have to supply, and 48 are in neither class. The gate closes when every reached cone of the final closure is shown total or has its caller precondition proved, or, failing that, when the owner records this as a retained trust row and the claim names it in its first sentence.

## The Pool boundary

The theorem proves nothing about the Pool program. It takes, as part of the description of the run, that every non-verifier action in the recorded transaction lineage is what the Pool and the runtime did, so settlement itself is not covered. The owner has still to decide between bringing the Pool's execution inside the security game, which would mean proving the Pool's consumer association, and reporting the claim as conditional on that association. Once the decision is recorded, the gate closes either with the proof or with the condition stated in the claim's first sentence.

## Repeated attempts

Within one experiment repeated attempts are fully covered, because the query budget counts every query the adversary makes, including repeats and every query made before a rejection. Across separately submitted spend attempts no theorem in the closure yet states a campaign bound. A stand-in theorem compiles (`RSL.MAT.campaign_charge`), giving a sum of the per-attempt bounds in which each attempt is charged for the verifier's hash calls of the earlier ones, at most 2,322 per attempt, with a factor of two for the current two-phase adversary; its three host obligations are not discharged, and whether the campaign corollary is published in these units is a decision on the scope of the contract. The gate closes when that reduction is proved at the host, or when the claim is worded per attempt only.

## Non-vacuity witness

A theorem whose hypotheses can never hold says nothing, so the release needs a witness that the description of the run can be met by a real run. Part of this is done: Lean shows that the game frame, the trace association and the first output are exactly the recorded facts, not `False`, and that the first output is inhabited. What is missing is a full inhabitant of the run description built from an actual accepted pair of deployed transactions; the devnet transactions are the natural source for it, and constructing it closes the gate.

## Trust reconciliation

Every trust row the theorem relies on is listed in [`TRUST-INVENTORY.md`](TRUST-INVENTORY.md), but the list has not yet been reconciled one to one with the final closure, several rows (among them the SDK borrow, standard-library, entrypoint-admission, persistence and SHA-256 value rows) have no recorded removal condition, 36 reviewed transcriptions lack a per-item removal condition, and rows added under the lead's standing delegation still need the owner's confirmation. The gate closes when the inventory matches the closure exactly, every row has its removal condition, and every row is either confirmed by the owner or named as unconfirmed.

## Smaller items

Three further items are recorded in the status document. One runtime-formatted panic path in the standard library's `RefCell` (`core/cell.rs:898`) has neither its reachability nor its exclusion proved; it can only abort a transaction, never make a false spend accepted, so it is a liveness caveat rather than a soundness one, and it closes with a proof either way or with the caveat stated. Parts of the work were compiled under Lean 4.31.0 and parts under 4.32.0, so the final build must name one pinned toolchain and recompile under it. And two readings in the run-7 assembly await the lead's confirmation: that the condition-(4) inclusion, restated over the current interface rather than the older one, satisfies the wording it was asked to meet, and that the averaged bound is acceptable in its present form of two separate facts (status document, section 7, item 12).
