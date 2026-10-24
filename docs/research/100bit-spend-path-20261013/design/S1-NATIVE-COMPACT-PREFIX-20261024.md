# Native compact prefix preservation, 2026-10-24

Status: checked accepted-only property of the actual extracted expand_semantic body. Full S1, S6 and the implementation-linked 100-bit target remain OPEN. No Rust or frozen artifact changed.

The accepted predecessor is 906005bffa. It pins the unchanged compact source, exact row_shape body, extraction tools and one open expand_values leaf. Its archival failed whole extraction is retained; no unchanged larger-cap retry ran.

## Enclosing source result

`AspisS1NativeCompactBodyFrame.semantic_root_prefix` states:

    ∀ ops input out expanded,
      compact.expand_semantic ops input out = ok (.Ok (), expanded) →
      ∀ j < 32, expanded.val[j]? = input.val[j]?

Here expand_semantic is the actual emitted native source body, including its checks, header copy, mutable lenses and Std.loop. Ops contains only the expand_values leaf. The theorem is universal in that leaf; it does not assume successful independent expansion, correct expanded values, parser acceptance, root equality or loop totality.

`body_frame` proves prefix preservation and nondecreasing destination on one actual emitted step. It covers ordinary payload copies, compact payload mutation, inner codec errors and final length checks. The successful mutable slice lens confines even an arbitrary returned replacement buffer to the suffix.

`loop_frame` composes those exact source steps through `Std.loop.fixpoint_induct`, using the checked accepted-result invariant theorem. It preserves the prefix on both codec Ok and Err loop returns, while allowing fail/div. The enclosing entry theorem then derives the initial 32 copied bytes from its own actual range-index, copy_from_slice and return-lens calls. All intermediate successful calls are obtained from this one enclosing source return.

These results remove a whole-native-expansion prefix-equality premise. They do not yet equate a returned Prepared root to a physical proof root: the actual prepare allocation/split/back/reindex/View/parser join is the next consumer. Row-2 root bytes additionally require the first three ordinary row steps through byte 79. Full expansion value correctness/totality, the actual leaf instance, SDK/account correspondence, original claim/powers association, complete PreparedBinding and final artifact re-pin remain open.

## Validation

Three focused dependent targets passed against the pinned warm cache, one local Lean job at a time with the atomic lock and -j1 -M4400. Body: 8.959 s, RSS 2260729856 bytes. Loop: 15.997 s, RSS 2236563456 bytes. Entry: 15.163 s, RSS 2259140608 bytes. All exit 0, zero swap, standard axioms only. Exact source/tool/import hashes and receipts are in s1-native-compact-prefix-targets.json and s1-native-compact-prefix-import-pins.json. No full replay, binaries or release closure claim.
