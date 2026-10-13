# Focused concrete extraction and binding evidence

Run `python3 validate_manifest.py` to validate the nine selected successful
receipts against their current source files. The validator also records the
failed attempts, exact runner/environment hashes, resource limits and base
git revision. It does not rerun Lean or audit the entire imported cache.

The build workspace is
`/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013` on the NUC.
Each target uses the guarded `compile-one.sh MODULE ATTEMPT` runner, with
MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0, TasksMax=128 and Lean -M5000.
The reservation guard counts active finite scopes recursively, reserving at
least 24 GiB for the external Docker scope group and at most 50 GiB in total
after adding a new 6 GiB job. An earlier guard briefly double-counted that
external reservation and refused launches; no compiler ran for those holds.

The original ConcreteProjection and InitialResponses import environments hit
Lean's memory limit. The replacements narrow existing imports without
changing their proof bodies and factor generic declarations away from
unused WideExact/masking specializations. The same memory caps then suffice.
The twelve import-only comparisons are recorded in `import-only-review.json`;
their focused rebuild receipts are in the adjacent import-footprint,
knowledge-import-narrowing and final-response folders.

TwoFoldExtraction's failed attempts exposed missing explicit dimensions and
a symbolic elaboration recursion limit. The corrected source supplies the
dimensions, uses named support lemmas and scopes maxRecDepth=4096 to the
composition theorem. ConcreteBinding uses the same scoped setting. Both
successful targets complete in under two seconds, below 3.1 GiB RSS, with no
swap and only standard axioms. No large concrete recurrence was evaluated.

The newest theorem scope and remaining obligations are documented in
`../../CONCRETE-BINDING.md`. First/second-restoration, final-response and
geometry receipts remain in their own adjacent folders. No full package,
frozen release manifest or unchanged runtime regression was run here.
