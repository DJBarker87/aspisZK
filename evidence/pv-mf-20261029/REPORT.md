# V346 — proved=shipped manifest (LOG D489)

**V346 remains P / OPEN. Privacy target not yet established.** This is a machine-checked, fail-closed inventory and source-identity audit, not a completed proof-to-shipped-source refinement. No historical proof, extraction or Kani certificate is migrated by name. V397, V398 and V399 remain open.

Release candidate: `85addf5a9764aa5e17d28bd6cf96bbda084447c5`. Branch: `codex/pv-mf-20261029`. Worktree: `/Users/dominic/ZK/.worktrees/pv-mf`. Host directory: `/home/dombarker/project-offloads/codex-pv-mf-20261029/`. No changes under `crates/` or `programs/`; no proofs, new Lean statements, Kani, wallet operations or key cleanup.

## Release target and reproduction

The fresh, offline, locked release build of `devnet_spend`, package `aspis-r1-cu-probe`, selects `r1p-check,aspis-r1-cost-probe/ct-host-prover`, rustc 1.94.1 (`e408947bfd200af42db322daf0fadfe7e26d3bd1`), LLVM 21.1.8, x86_64 Linux. All **553** recorded project/build input files match candidate git blobs and the read-only fscan host snapshot. This includes both lockfiles and root/tool Cargo manifests. `resolved-features.json` retains **487** actual Cargo fingerprint records; it is an inventory of build units, not an assertion that every unit is linked.

`native02-receipt.json`: exit 0, **113.7548 s**, peak aggregate cgroup memory **4,857,675,776 bytes**, swap 0. The exact command, environment, wrapper and compiler output are retained. Cargo package-specific overflow-check overrides remain enabled where Cargo.toml specifies them; generic release defaults must not be substituted. The inherited workspace lacks `.cargo/config.toml`, whose only setting is an unused xtask alias; this is explicitly recorded in `BUILD-CONTEXT.json`.

| Artifact | SHA-256 | Result |
|---|---|---|
| devnet_spend, 2,619,224 bytes | `fa888460b2c37bee087afd6289cd55219fe2732ea1e1c75011147ed15c260348` | Fresh build equals pv-l3a |
| default ELF | `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4` | Retained ELF freshly verified |
| devnet ELF | `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299` | Retained ELF freshly verified |
| Pool ELF | `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548` | Retained ELF freshly verified |

`native03-receipt.json` rehashes all four artifacts in a separate admitted capped scope. ELFs were not rebuilt. The client is retained securely under this job's `bin/devnet_spend`; its Cargo target cache was removed. `PROTOCOL.json` pins wire/parameter-defining files and literal constants from the build inputs. Conditional alternatives remain explicit; effective configuration is bound by the resolved features and reproduced binary, not by interpreting an inactive source constant.

## Map and evidence classes

`MANIFEST.json` is the entrypoint. Tables can be sharded or compressed; `PV_MF_check.py` verifies both compressed and uncompressed hashes and loads them transparently.

- `MODULES.json`: 8,004 conservative root paths (all tracked PV_* Lean filenames and all R1Z paths), 15,877 paths after following import candidates, declarations, source/function mentions and receipt references. Historical tracked variants are separate records. **10,265 import edges have multiple candidates**; **1,625 have no tracked candidate** (external or missing). No variant is adopted merely because its basename matches. `COHORTS.json` retains EJR source authority; no compiled objects were loaded or substituted.
- `BINDING-MODULES.json` and `BINDINGS.json`: module/blob index and 28,989 exact generated Rust-name/source-location to Lean-declaration records, over 1,826 distinct extraction blobs and 2,395 module paths. Candidate source files carry git blob and SHA-256 identities. Generated banners alone supply no generation hash chain or deployed-feature parity credit.
- `SOURCE-BINDINGS.json`: 20 structured own-1 records whose Rust file, exact line span/body hash and Lean model match the candidate. These retain the receipt's partial scope. Source identity is verified; semantic sufficiency and whole-row restoration are not re-audited.
- `EVIDENCE.json`, `HASH-CLAIMS.json` and `SUPPLEMENT.json`: receipt/docstring discovery, file-pin comparisons and additional historical extraction/native/Kani receipt references. Original evidence-class labels remain in pinned receipts; module-text class mentions are labelled as mentions. The own-2''' harness label, b3p6-1 reclassification label, extraction, finite native differential and Kani are not interchangeable. No Kani PASS is re-credited; K-1/K-2 restrictions remain.
- `RECOUNT9.json`: 407 supplemental privacy recount-9 rows, frozen at research `47f44e887a502ad865ca0635745eae7cc4ac7b3b`. Those rows are absent from the release candidate. Every recorded definition witness is compared against the candidate; historical status is retained only as historical data.

## Stale associations and gaps

The complete lists are `STALE.json`, `HASH-REVIEW.json` and `GAPS.json`; their final counts are recorded below. **764 stale-association records** remain, including **175 stale recount-9 witness references**. **944** span/token/file comparisons require separate review; they are not asserted to be stale files. The raw inventory contains **138,196** receipt hash comparisons. Each stale record names the receipt/pointer or recount row and both identities. Span/token hashes are kept separate from whole-file hashes. Examples of old source identity records that cannot migrate include `pv-batch2-20261027/SOURCE-IDENTITY.json` for `prover.rs`, `host_semantic.rs` and `r1_wire.rs`, and `pv-cb3-20261026/RESUME6_SOURCE_IDENTITY.json` for `host_transcript.rs`. These are stale historical pins, not an assertion that every theorem in those jobs is currently invalid.

`GAPS.json` includes **28,392 distinct inventory keys** from pv-l3a's linked function index, all 46 pv-diag shards and the pv-b3p6 inventories. **28,156 lack an exact discovered extraction-function-name association.** Exact matches are discovery links and do not establish source-origin fidelity. The two pv-diag MIR inputs with mismatched recorded hashes are excluded and named in the manifest.

The supplied inventories do not certify the complete set of actually reached privacy-path functions: pv-diag includes unlinked candidates and explicitly lacks whole-image effect closure; pv-l3a omits inlined instances; b3p6 retains cfg/reachability obligations. Consequently this conservative gap inventory cannot honestly be represented as an exhaustive theorem about reached functions. Missing generation chains, feature/profile associations, accepted source cohorts and complete call-cone coverage remain explicit blockers.

## Validation and retained obligations

Run repository/receipt integrity checks with:

```sh
python3 evidence/pv-mf-20261029/PV_MF_check.py
```

Use `--release-gate` for the release decision: it deliberately exits 1 while V346 is OPEN. The gate also checks the actual stale/gap/cohort tables and unresolved obligations; changing the status string alone cannot make it pass. `--host` additionally requests a fresh admitted/capped artifact rehash and checks returned hashes against this manifest; reservation refusals remain failures to launch, never admissions. Source and proof hashes are checked at both the pinned release revision and current HEAD, with uncommitted source changes rejected.

Reconstruction order: `PV_MF_manifest.py`, `PV_MF_bindings.py`, `PV_MF_supplement.py`, `PV_MF_source_spans.py`, `PV_MF_finalize.py`, `PV_MF_pack.py`, then `PV_MF_check.py`. Native artifacts/receipts are separate inputs, generated by the recorded native launcher; rebuilding is not part of an ordinary manifest check.

The checker passed integrity validation, refused the OPEN release gate, rejected an intentionally zeroed client digest, and rejected a CLOSED status string unsupported by the association tables; the original artifact record was restored byte for byte. Results: `validation.json`, `release-gate-validation.json`, `negative-control.json`.

Budget: **0/20 Lean**, **3/30 native scopes**, **0 Kani**. Every native scope used admission plus 6G/8G/swap0/64-task caps. Native01 stopped before compilation because SSH PATH omitted rustc; its missing wall/peak/swap measurements are recorded explicitly, not invented. Native02 corrected this job's wrapper PATH and succeeded; native03 performed the retained-artifact hashes. No shared infrastructure was edited and no refused/void compilation was credited.

Premises removed: **none**. Before/after V346: same required proved=shipped association, still OPEN, now with checked artifact identities and explicit stale/gap records. No premise, observer, simulator or trust field was weakened, added or moved into T. V370/compiler preservation (D381/D386), rdea-1, complete source/extraction/Kani associations, V397 replay, V398 axioms audit and V399 final release binding remain. No checked witness-dependent privacy counterexample is claimed. Next deliverable: choose the authoritative candidate cohort and supply missing generation/source-binding chains for the explicitly listed function/module associations, then replay/audit that adopted closure.
