# TX1 composition frontier

Status: OPEN. Headline `AspisR1.RPx_Deployed.deployed`. Frozen source
`4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`; digest/error slots op43/op44.
L154, narrowed D188, frozen3, approved runtime persistence and game unchanged.

The fixture theorem `JHq_TX1.accepted1_saved` and byte implication
`JHn_ExactReturned.source` are fixed-input results. They cannot supply an
arbitrary native accepted-run refinement. Their checkpoint is not an independent
witness that may be substituted into another accepted execution.

`NCL_DriverCuts.accepted` extracts shape, scan, zero, prepare, actual root
range/copy, accumulator, batch, geometry, pending, query, flush and checkpoint
observations from ONE existing emitted-driver success, with identical proof,
public bytes, digest object, hash and saved Vec. `NCL_DriverForward.source`
is the corresponding symbolic outer-control replay. These are model theorems;
they do not certify the Rust driver or supply any missing lower bridge.

## Lower-unit audit (not invented hypotheses)

The exact owner bridge statements are not yet present as complete closed native
refinements. The following are required interfaces, NOT defined Prop aliases,
axioms, or accepted hypotheses. No unused `True` hypothesis or disguised whole
TX1 conclusion is introduced to satisfy the spelling requirement. The requested
full eighteen-hypothesis theorem remains OPEN until these interfaces and their
caller domains can be instantiated against the actual owners.

| Required hypothesis | Owning work / exact local obligation |
|---|---|
|NCL_Lower_alloc|NCD_/allocation: actual filled/reserve/initialization Result and carrier; 14759 byte logical allocation and 64 canonical weights; preserve allocation errors.|
|NCL_Lower_residue|residue lane: actual pending new/update/finish on same64 rows, terms=i, per-group overflow bounds and same flushed weight allocation.|
|NCL_Lower_accumulate|accumulate lane: one actual S2 query step, i<10, same rho/power/rhs, next and pending terms advance together.|
|NCL_Lower_oracle|runtime oracle lane: exact ordered borrowed slices and unchanged32-byte syscall reply; digest value remains approved runtime trust.|
|NCL_Lower_multiproof|NBV_/NBY_/NCE_: same binary idx/val scratch, sorted distinct active indices<2^18, n<=10, supplied-node cursor/padding and chronological digests/errors.|
|NCL_Lower_parser|NBR_/NCA_: same compact proof57607, actual Prefix, semantic13831/y1 928 producer buffers and all framing/validation errors.|
|NCL_Lower_keys|NBV_/NBY_: keys from same22 prepared queries, tree0/1/2, active batch0 n10, same opening slices and sorted duplicate-folded prefix.|
|NCL_Lower_batch|NBV_/NBY_/NCE_: actual three authenticated tree calls from same Prepared/root/proof/scratch, first-error prefix and ordered logs.|
|NCL_Lower_dots|dots lane: same authenticated opening832, g29 canonical, four dot carriers and checked private-Q domain.|
|NCL_Lower_geometry|geometry lane: same22 distinct indices<2^18; range0..10, fifty inverses and five nonzero denominators/query.|
|NCL_Lower_public_hash|public-hash lane: same validated statement, canonical field/state inputs, actual serialization and returned root/hash.|
|NCL_Lower_sampler|sampler lane: exact same32-byte block, canonical ordinary/gamma output, nonzero gamma and preserved retry/error behavior.|
|NCL_Lower_semantic_eval|S1 read-only cohort: same genuine parsed Claims/Public/challenges, decoded canonical coefficients and actual terminal return.|
|NCL_Lower_semantic_transcript|NBR_/NCA_/NCH_: same Prefix and semantic bytes, row order, CircleRows, blocks, first error and all digest attempts.|
|NCL_Lower_opening_transcript|NBR_/NCA_/NCH_: actual sem finish, y1/inactive/round/root/final windows, same powers29 and prepared-claim operands/return.|
|NCL_Lower_prepare|NBR_/NCA_/NCH_: actual prepare own allocation/split/child/return control on proof57607, logical14759, validated Public, same Prepared/g29.|
|NCL_Lower_query|NBO_/NBW_/NBZ_/NCG_: actual one native query iteration and induction to10 on same authenticated Prepared/proof/g29, geometry and accumulator/pending.|
|NCL_Lower_shape|shape lane: actual parse_shape and full scan of same57607 bytes; compact464 and every wide/opening canonicality domain.|
|NCL_Lower_checkpoint|KND_: SUSPENDED local checkpoint bridge; same p/a/proof57607/public1880, next10,64 canonical weights, ordered three digests, exact1768 output.|

CLOSED leaf packets must be imported within the above domains. No XRn_Join
kit, stand-in, independently supplied checkpoint, or unproved canonicality
assertion is used. Current model cuts alone do not prove these natural domains.

## Checked model milestone

`NCL_WrapperToDriver.source` derives the actual decoded/validated statement,
physical public bytes, selected proof suffix, split10 and SAME returned saved
Vec from the headline-shaped first-wrapper model premise. Its heap conclusion
is the actual writeBracket of that saved Vec under the existing TrustedStd
contract. `NCL_TX1ModelChain.source` composes it with the actual driver cut
inversion, derives proof length57607 and raw=take688++suffix, and retains that
same driver acceptance and Nonempty complete cut record. No source cut or
second successful run is supplied by the caller.

Accepted attempts: L004 (cut inversion), L013 (forward replay), L016 (wrapper
to driver), L017 (composed model chain). Each prints standard-only axioms.
L001 is inspection only. Other L002–L017 drafts are excluded failures, not
proofs. Exact receipts record target/command, source revision/hash, direct
object/sidecar hashes, wall/RSS/swap and all printed axiom lines.

This is a partial stage-one milestone, NOT the requested full native/lower-unit
composition. It adds or discharges no native refinement premise. In particular
saved length1768, actual native entry dispatch, exact Rust buffer retention,
canonical child domains, ordered native oracle effects and source/ELF binding
are not established by these new theorems. The fixture is not substituted for
the arbitrary input. Stage two begins with independent childless/early-error
native bodies rather than assuming an open lower member.

Allocation: use the stricter simultaneous limits stated by the prompt: at most
80 Lean attempts and50 Kani invocations (despite the later60-Kani job figure).
One capped scope at a time, -M7000,6G/8G/Swap0/Tasks64. Private cache retained.
