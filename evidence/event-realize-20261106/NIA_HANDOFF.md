# NIA native event realization handoff

Branch: codex/cx-event-realize-20261106. Work in progress; target not yet established.

Scope: NFS event interpretation, complete prepared-constructor traces, failed/diverging scalar packets, then conditional TX1 cut composition. Only NIA modules and this evidence directory may change. No shipped source edits, pushes, wallet operations or sibling worktree edits.

Budget: 40 Kani, 80 Lean, 1 extraction (NHR_stage.py only). Serial admitted scopes, MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64; Lean -M7000. Host disk observed 97% used (57G free); retain a small own cache and reuse coherent pinned objects.

Initial inspection: NHZ events_from_cuts is conditional on physical packet existence and exact native ordering. NFS cuts record NFP callee events; arbitrary base callback slots survive NFS_QueryOps.installed. Result equality alone does not prove empty digest effects. NHS_PreparedPacket.source currently proves only successful Result, and NHS_QueryFailures covers Result Error/fail/div without earlier scalar events. NGT successful Block has three ok edges only. No trace or native credit is claimed yet.

Retained hypotheses: op9 and full native parent ordering, physical observer fields, approved runtime trust rows and original L154 parameters. No row promotion expected.

Validation, exact targets, source/dependency hashes, revision, exit/wall/RSS/swap and printed axioms will be recorded in NIA_ATTEMPTS.jsonl and per-attempt receipts. No ELF rebuild is triggered unless shipped source changes (none planned).

Stage 1: NIA_L002 passes (8.31 s, 5,993,380 KiB, swap 0); six top theorems have standard axioms. This is structural interpreter algebra only; the native installation gap is explicit in NIA_FAILING_STEP.md. L001 launched no Lean process: missing IDb_Components object; owned input corrected by making the retained NFS base explicit, with no claim of native discharge.

Stage 2 model result: NIA_ConstructorTrace.source and frame construct a complete ordered NGQ_Cuts.Trace with the exact NGN_Emitted.prepared Result for every branch, including all earlier scalar/replay events. No successful-constructor or complete-Trace premise is accepted. The code retains one seed read, S1-S4 block reads, the existing query code, S6 block reads and pure claim/powers branches. claim_dictionary proves by definitional equality that the actual installed claim ignores its digest dictionary. L005/L007/L009 pass with standard axioms. This is a full MODEL reification; native failed/diverging scalar provenance and native constructor logging installation are not supplied by canonical evaluation. Box allocation is outside NGN_Emitted.prepared, and is not silently included in this theorem. No row promotion.

Stage 3: NIA_L011 proves every block stop prefix (tag, absorb, read, advance; fail and div) and propagates it through scalar/scalar_k with exact full log and arbitrary prior-log framing. These are partial-dictionary MODEL packets, not native failure certificates. NIA_STUBS.md records why no native Err constructor or short-payload rejection is available at the frozen signatures. Existing NGT ok-edge laws were not edited.

Stage 4: L013 adds exhaustive block coverage (no assumed failed packet); L021 consumes the SAME NHS/NHK query invocation in exact constructor Error/fail/div prefixes. L020 strengthens the event interpreter to NFS_CallerDomains.ops, whose no_seed theorem fixes every callback; the earlier arbitrary-base interpretation is superseded. This removes arbitrary callback dependence in the interpreter, not native effect provenance. L022 exports constructor_cut/constructor_extension and literally calls NHZ_DRIVER.events_from_cuts in events_from_constructor, retaining the full code ordering hypothesis. L023 imports all this with NGK_COMBINED_IMPORT and RPx_Deployed.deployed; standard axioms only. The existential observation there is constructed from the model and is not identified with physical TX1. Full parent native ordering/op9, loop event realization, scalar/Box abort boundaries and the five same_law physical fields remain open. No row promotions.
