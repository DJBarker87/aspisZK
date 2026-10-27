# Shared extraction obstruction inventory

Snapshot: branch codex/pv-extract-20261027, base 7599dff5b274d52324ae8681664f6b343f9a81ac. Read-only `git grep -n -i -E 'ProverRwRngExtractor006|loan validation' <branch> -- evidence/` over every local `codex/pv-*` branch (including cb3, cblib, cbmid, runjoin, join, srcid3). Full results: inventory-grep.txt. Branch revisions and 27 distinct extraction targets: inventory-inputs.json. LLBC signature/source inspection: inventory-llbc.json. Historical log refusals are authoritative for those runs; a currently present mutable host LLBC is diagnostic input, not retroactively the historical input unless its hash matches the original receipt.

The exact reference-output refusal occurs for these 15 distinct ops. D = the same log also contains `structured Drop requires destructor semantics`. Paths beginning with a crate/version refer to pinned registry source. The guard is whole-crate: a reference in a helper output suffices even when the root returns a value.

| op / row | Shipped function, source location | Exact borrow pattern / helper triggering reference-output scan | Evidence branch / variant; other guard |
|---|---|---|---|
| 36 / V187 | `<[T; N]>::try_from(Vec<T>)`, nightly-2026-06-01 library/alloc/src/vec/mod.rs:4534; candidate-owned references only | borrowed reference variant dereferences `&Vec` to `&[T]`; owned variant indexes `v[i]` through reference-returning Vec/Index methods. These logs do **not** establish rejection of the shipped generic conversion itself | cblib: op36-full-opt-first-02; op36-owned-opt-direct2-01 (D) |
| 79 / V201 | `r0::encoder::eval_message`, crates/aspis-core/src/r0/encoder.rs:28, calls eval_pair:10 | `for (pair,n) in q.chunks_exact(2).zip(basis)`; `ChunksExact::next` returns `Option<&[E]>` | cb3 source-resume6-retry2; cbmid op79-001 (D) |
| 132 / V228 | `pool_v1_pair_forest_relation_free_mask_cells_v1`, crates/aspis-statement/src/pool_v1/pair_forest_hiding.rs:233 | calls schedule:120; `for scheduled in &mut links` (:136); borrowed links in `endpoint_counts` (:101-106); Vec deref and Iter/IterMut next | cb3 source-resume6host007; cbmid op132-001 (D) |
| 133 / V229 | `pool_v1_pair_forest_copy_active_rows_v1`, same file:179 | same schedule mut iterator; `into_iter().flat_map(...).collect()` then `sort_unstable`/`dedup` through Vec deref_mut | cb3 source-resume6host007; cbmid op133-001 (D) |
| 205 / V231 | `Sha256VarCore::finalize_variable_core`, sha2-0.10.9/src/core_api.rs:60 | mut buffer/output; padding closure; `out.chunks_exact_mut(4).zip(state.iter())`; block_buffer sealed.rs:21 `split_blocks` returns two borrowed slices | cblib op205-opt-frontier-01 (D) |
| 212 / V234 | `Digest::finalize`, digest-0.10.7/src/digest.rs:85 | owned self, creates mutable output, calls FixedOutput; GenericArray deref/deref_mut and iterator methods return refs; downstream split_blocks returns slices | cb3 wrapper-resume6host006; cblib op212-002 (D) |
| 215 / V235 | `CoreWrapper::finalize_into`, digest-0.10.7/src/core_api/wrapper.rs:170 | owned self + `&mut Output<Self>`; forwards `&mut self.core`, `&mut self.buffer`; block-buffer split_blocks returns borrowed slices | cb3 wrapper-resume6host006; cblib opt-frontier-01 (D) |
| 216 / V236 | `CoreWrapper::update`, same wrapper.rs:148 | `&mut self`, `&[u8]`, `buffer.digest_blocks(input, |blocks| ...)`; split_blocks returns `(&[Block<N>], &[u8])` | cb3 wrapper-resume6host003; cblib opt-frontier-01 (D) |
| 217 / V237 | `CoreWrapper::default`, same wrapper.rs:23 (`#[derive(Default)]`) | root returns owned Self; included GenericArray iterator/deref closure contains ref-returning helper declarations, not a reference escaping default | cb3 wrapper-resume6host002 (D) |
| 219 / V238 | `CtVariableCoreWrapper::finalize_fixed_core`, digest-0.10.7/src/core_api/ct_variable.rs:114 | `&mut self`, `&mut Buffer`, `&mut Output`; temporary GenericArray then output slice copy, ref-returning deref/index/raw slice helpers | cb3 wrapper-resume6host002 (D) |
| 222 / V239 | `multilinear_evaluate_qm31`, crates/aspis-statement/src/constraints_v4.rs:782 | sparse_eq_weights (:601) uses point.iter().rev().take_while; shared iterator next/back returns `Option<&QM31>`; column indexing borrows | cbmid op222-001 (D) |
| 223 / V240 | `compress_tagged_tuple`, crates/aspis-statement/src/logup.rs:75 | `for value in values` (:78) yields `&M31`; `Iter::next` output `Option<&M31>`. Root returns QM31 by value | cb narrow/opt, transparent inline/by-value; cb3 built; no D |
| 224 / V241 | `build_pool_v1_pair_forest_copy_helper_v1`, crates/aspis-statement/src/pool_v1/pair_forest_semantic_oracle.rs:171 | shared trace borrow; copy-terms `Vec::deref` returns slice; calls shared helper builders and `.map_err(...)` | cbmid op224-001 (D) |
| 249 / V256 | `gamma_sample`, crates/aspis-r1-cost-probe/src/sampler.rs:111 | low_base_p_digits:56 uses `quotient.iter_mut().rev()` (:61); add_small_base_p:89 `for digit in digits` (:91) yields `&mut u32`; indexing and slice try_into | cb3 op249-opt-resume6forcefix1 (D) |
| 258 / V264 | `all_slots_clear`, crates/aspis-r1-cost-probe/src/ct_pole.rs:18 | `values.iter().enumerate()` (:20), `for side in sides` (:22), `for value in side` (:23); shared Iter::next reference output | cb3 op258-opt-resume6host002; no D |

Additional V240 support obstruction: `translate_aux_tuple`, crates/aspis-statement/src/pool_v1/pair_forest_trace.rs:522, uses `for limb in &mut tuple...` (source text and exact span in inventory-llbc.json); cb op223Aux-resume5-aux-r03. It is not a new callback row.

Separate failures, not misclassified as this refusal: op109 has Drop-only refusals (later source law exists); op121 Drop-only; op251/252 have other direct-extraction failures; owned op253 fails internal shared-loan cleanup after passing this preflight. Native runjoin records show Drop-only refusals. A generic report saying “loan/Drop” does not imply the exact escaping-reference guard fired.

Budget tally: Lean 0/60, Kani 0/0. Next unused Env-J ID 42400; no ID allocated by inventory/OCaml work. No shipped source, callback dictionary, endpoint premise, wallet or key changed.

## CB9 direct-root additions

Pinned extractor unchanged; preflight enabled. These are extraction obstructions, not checked counterexamples. No Kani arithmetic retry or prover-local copy is authorized.

### op226 / V243

Status: REFUSED (OPEN). Direct shipped root `aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public::public_bytes`.

```text
   "ProverRwRngExtractor006: fail-closed preflight: escaping reference output requires loan validation; structured Drop requires destructor semantics")
```

Receipt: `cb9-op226-aeneas/receipt.json`; full log: `cb9-op226-aeneas/output.log`. No source theorem, no row credit, no counterexample.

### op227 / V244

Status: REFUSED (OPEN). Direct shipped root `aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public::terminal_qm31`.

```text
   "ProverRwRngExtractor006: fail-closed preflight: escaping reference output requires loan validation; structured Drop requires destructor semantics")
```

Receipt: `cb9-op227-aeneas/receipt.json`; full log: `cb9-op227-aeneas/output.log`. No source theorem, no row credit, no counterexample.

### op228 / V245

Status: REFUSED (OPEN). Direct shipped root `aspis_statement::pool_v1::pair_forest_trace::build_pool_v1_pair_forest_copy_registry_v1`.

```text
   "ProverRwRngExtractor006: fail-closed preflight: escaping reference output requires loan validation; structured Drop requires destructor semantics")
```

Receipt: `cb9-op228-aeneas/receipt.json`; full log: `cb9-op228-aeneas/output.log`. No source theorem, no row credit, no counterexample.

### op230 / V247

Status: REFUSED (OPEN). Direct shipped root `aspis_statement::state_only_semantic::state_only_copy_helper_sum`.

```text
   "ProverRwRngExtractor006: fail-closed preflight: escaping reference output requires loan validation")
```

Receipt: `cb9-op230-aeneas/receipt.json`; full log: `cb9-op230-aeneas/output.log`. No source theorem, no row credit, no counterexample.

### op250 / V257

Status: REFUSED (OPEN). Direct shipped root `aspis_r1_cost_probe::sampler::ordinary_sample`.

```text
   "ProverRwRngExtractor006: fail-closed preflight: escaping reference output requires loan validation; structured Drop requires destructor semantics")
```

Receipt: `cb9-op250-aeneas/receipt.json`; full log: `cb9-op250-aeneas/output.log`. No source theorem, no row credit, no counterexample.

### op254 / V261

Status: REFUSED (OPEN). Direct shipped root `aspis_r1_cost_probe::weights::powers`.

```text
[Error] Nested-loop returns require exactly one Option language item
Source: '/home/dombarker/project-offloads/codex-pv-cb3-20261026/source/crates/aspis-r1-cost-probe/src/weights.rs', lines 7:0-7:40
Compiler source: PrePasses.ml, line 840
   \nSource: '/home/dombarker/project-offloads/codex-pv-cb3-20261026/source/crates/aspis-r1-cost-probe/src/weights.rs', lines 7:0-7:40\
   \nCompiler source: PrePasses.ml, line 840")
```

Receipt: `cb9-op254-aeneas/receipt.json`; full log: `cb9-op254-aeneas/output.log`. No source theorem, no row credit, no counterexample.
