# Reproduce the source-only NBI2 inventory

The delivered Markdown/JSON and validation receipt are sufficient to review the result.
The large intermediate AST and declaration indexes are intentionally not committed.
Only this evidence directory and a job-prefixed temporary Python dependency directory
are used. No Rust, Kani, Lean, SBF, host reservation, compiled object cache, wallet or
key operation is involved.

To regenerate, install `tree-sitter==0.25.2` and `tree-sitter-rust==0.24.2` into
`/private/tmp/NBI2-parser` using Python pip's `--no-cache-dir --target` options.
The initial0.26.0 parser bus-faulted twice during inspection (exit138);0.25.2 completed.
This was a Python source-tool failure, not a proof timeout/memory kill or Rust run.
The repair affects only this worker's scripts/dependencies, not host infrastructure.

Run these scripts in order, waiting for each to finish:

```sh
python3 -B evidence/native-inv2-20261027/NBI2_inventory.py
python3 -B evidence/native-inv2-20261027/NBI2_cohorts.py
python3 -B evidence/native-inv2-20261027/NBI2_select.py
python3 -B evidence/native-inv2-20261027/NBI2_map.py
python3 -B evidence/native-inv2-20261027/NBI2_finish.py
python3 -B evidence/native-inv2-20261027/NBI2_render.py
python3 -B evidence/native-inv2-20261027/NBI2_validate.py
```

The validation script can run alone against the delivered JSON and immutable git
revision. It checks frozen file/body hashes, cohort constant membership and source
snapshot hashes, graph/domain references, topological order and source isolation.
It does not validate semantic equality or prove exact compiler reachability.
The resolver deliberately records conservative field receiver alternatives, and
classifies standard/runtime calls separately; review those alternatives before
commissioning each native bridge. Anonymous closures belong to their caller; the
macro-generated FibreIndex methods cite the template and invocation.

The cohort map is based on the retained RPx/RPv plans and kernel dependency set.
It distinguishes the concrete installed op22 encoder from the still abstract op53
emitter; fixture-only JHb installations are not credited to the headline.
When a helper lacks a separate cohort definition, the record either identifies
a parent/model context or flags the encompassing abstract boundary. Absence of a
separate helper definition alone is not evidence of a soundness error.

Native source features and ID overrides are pinned by the inherited Low2 command
receipts. No ELF hashes are newly reproduced. All thirteen CLOSED opaque leaves
are cited; only private canonical::Dot::push is reached on this TX2 path. The other
twelve are TX1/preparation predecessors, not fresh TX2 calls. S2LeadInterface's
scope separates later Pool settlement/CPI from this verifier invocation.

The final receipts cover source reading only: Lean0/30, Kani0/0, Rust0/0.
No new theorem means no new #print axioms target; the axioms field is N/A.
No assumption or headline premise is discharged or changed. Target not yet
established.
