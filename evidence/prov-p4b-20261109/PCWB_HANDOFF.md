# PCWB_ handoff: phase P4b (reference and cut-crate lane, part B)

Target not yet established. No ledger row, trust row, RSL, security contract or shipped source was changed; no Kani was run; nothing was pushed or merged. Branch codex/pc-prov-p4b-20261109; host workspace /home/dombarker/project-offloads/codex-pc-prov-p4b-20261109/.

## Claims established (references in this directory)

1. **NHV_NEO_WindowV2, NHV_NEO_ParserRef, NHV_NEB_AdditiveRef (Funs and Types, 6 modules).** Source located in the research tree and committed under sources/ with sha256 (neo_window 2e024055, neo_parser 1943f54c, neb_additive c0941595). Re-extraction PCWB_E001-E003 (XRa_bin charon daad69be and aeneas c0cf4fcc, the pair recorded by the original NEO_/NEB_ receipts) is byte-identical to the retained outputs and to the live NHV modules after removing the import lines. 18 equality theorems (5+3+10 declarations) compile in PCWB_L001 (exit 0, axioms propext/Classical.choice/Quot.sound only). The Kani receipts NEO_K053-K057 and NEB_K009 (exit 0) name the same source hashes (PCWB_KANI_LINKS.json K3; hash identity only, harness contracts not audited).
2. **MultiproofConeRef, MultiproofParserRef, MultiproofSortRef.** Sources located (tools/multiproof-cone-20261021 at commits d28944b2a05 and 8c029994865), committed, re-extracted with frozen aspis-core 4bb3b3f staged by the unchanged NHR stager (PCWB_E004-E007). Funs of all three equal the live modules byte for byte; ParserRef Types too; ConeRef/SortRef Types differ only by post-processing items classified in PCWB_CLASSIFICATIONS.json C4. Equalities: 29 theorems compile in PCWB_L003 (exit 0, standard axioms only). Four definitions are commented P3 obligations: reference.level_rows, reference.levels, reference.verify_owned (ConeRef) and sort_reference.sort_rows (SortRef); the first three and last are partial_fixpoint definitions whose two sides unfold to distinct Lean.Order.fix constants (PCWB_L004 probe).
3. **Kani hash mismatch (K1).** Exit-0 Kani receipts name reference.rs e812aae3; the live cone module came from 32548b0d; the files differ only by two cfg(kani) attributes; PCWB_E007 shows the extraction is unchanged except a line-number comment. Reported, not resolved (D3).
4. **Cut-crate lane, WithdrawalCaller (`encode_digest_canonical`), SemanticCall, BatchedWeights.** Their live modules are byte-identical to files generated inside retained archives that also hold the LLBC, the input crate and the receipts; PCWB_LLBC_COMPARE.json shows Charon re-run on the committed inputs reproduces the archived LLBC (all fields equal, short_names equal up to order) and the LLBC embeds the committed source hashes. The Aeneas step could not be repeated: the host build crashes on all three (E008-E010; shape retired, C5), the original binary 959659a6 is not on the host (D2). No equality theorem is claimed for these.
5. **copy_chunk (S1ValuesOwnedModelV1): source not found** after the full search (D1).
6. **Triage of the remaining 65 cut modules** (PCWB_CUT_TRIAGE.json): tree search only; nothing re-extracted.

## Assumptions

Added/changed/discharged: none. Equalities are against the gate constants; they do not remove any gate hand model: PCWB_HAND_MODELS.json records that none of the six modules with equalities resolves an external name to a hand-written gate model.

## What ran

12 extraction scope slots used 10 (E001-E010; E008-E010 failed in Aeneas), Lean 4 of 12 (L001 exit 0, L002 probe exit 1 expected, L003 exit 0, L004 probe exit 1 by design), Kani 0. Per-scope target, command, source revision, exit, wall, peak RSS, swaps, axioms: PCWB_SCOPES.json and PCWB_E###/PCWB_L###/receipt.json; admission JSON per scope (host scopes < 6, Stream C < 3, disk >= 40 GB, allowed:true). Largest RSS: L001 5.95 GiB (cap 8 GiB, MemoryHigh 6 GiB); extraction peak 0.6 GiB (cap 4 GiB); no kill, no timeout, no cap raised.

## Remaining

D1-D4 of PCWB_DECISIONS_NEEDED.md; the P3 proofs of the four partial_fixpoint equalities (fixpoint induction: fresh ⊑ gate and gate ⊑ fresh with antisymmetry); rebuild or accept the Aeneas binary for the archived packets; the QRaw items; FIn_ExtractFuns (b1) and the NHI_/NEI_/NEV_/NFS_/NGD_/NGM_/NHJ_ modules (P4a).
