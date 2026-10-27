# pv-reach8 / LOG D327: reuse preflight and budget review

Step 1 is **not complete**. InstalledOp84 was not compiled. No proof result or
premise removal is claimed. This is a read-only feasibility finding, not a
counterexample or a cohort-inconsistency finding from Lean.

The exact 200 prerequisites are in `prerequisites-before.txt` and the per-module
source/import records in `project-closure.json`. All 200 are transitively needed
by CandidateCore, hence InstalledOp84; none is an unrelated extra root. The h5
sources were checked again against git HEAD ff32e6963640608feef157f8cdd445d12e74daab.
EJR/freeze precedence and the two h5-prime source differences remain unchanged.

## What the h6 search found

The requested runjoin20 `project-hash-check.json` records 669 project objects.
Its overlap with these 200 prerequisites is **zero**. The endpoint certificate
does not certify everything incidentally present in runjoin20's object directory.

The read-only search covered every `codex-pv-*` host directory, excluding build
targets, git and node_modules. It found candidate paths for all 200 modules.
The candidates resolve to Stream B join/cb directories, the shared env-J tree,
or `codex-cx-prover-rw-20261023`. No candidate was copied, linked or imported.
In particular, lookup through a runjoin symlink was not treated as permission
to load an object from a Stream A directory.

The join candidate manifest records matching sources for 147 prerequisites,
but explicitly describes a **surviving copied candidate cache; no local
compiler invoked**. It has no complete build dependency fingerprint or
historical compile environment. Successful committed Stream B receipts with
matching source hashes were found for 67 of the 200 modules; the two sets
overlap. A source match is only the first h6 check.

`h6-prerequisite-dispositions.json` gives each module's source check, transitive
object comparison and environment check. The complete object maps are in
`environment-fingerprints.json`; dependency selection is reproducible from
`project-closure.json`. The comparison includes every transitive project import
and, conservatively, the entire 5,673-object h4 external cohort. It is a current
effective-object comparison, **not** an assertion that current directory
contents reconstruct an unrecorded historical build fingerprint.

For runjoin20, 188 prerequisites have at least one differently hashed dependency
from the objects this job would otherwise load; 179 have transitive prerequisites
still unavailable in this job's private root. These categories overlap. The
available candidate environments do not have this job's literal LEAN_PATH
prefix. Environments not recorded for an original build remain unverified;
no path-equivalence waiver or historical environment identity is inferred.

For a concrete independent failure, cb attempt 27138 compiled PV_CB_Op84Exact
with PV_CB_Op84Funs hash
`d2cc6d66db691b449914a35e329659c442d650ed6550c65b8a37967566220be4`.
This job would load
`db6abf0c2ce6626fc27fada5aa7493f36bf6f9e2658f3c6d27f83d40d2cd6ce7`.
The same receipt requires PV_CB_Merkle, which is still privately absent.
Neither source equality nor an accepted historical compile resolves this
dependency-hash mismatch.

**Zero candidates were verified against all three h6 conditions.** This means
none can be credited as reusable by this run; it does not assert that no further
provenance evidence could ever qualify a candidate. The source-authority rules
were not relaxed to make a cache fit.

## Concrete estimate and decision

With presently verified evidence: 200 existing prerequisite modules need private
builds, followed by one InstalledOp84 module containing one new theorem
(`installed_noCatch`): **at least 201 compile attempts**, before any new work on
the requested complete reachability claims. This count assumes no failure or
retry. Three audit attempts would increase it to 204.

Even the deliberately optimistic alternative that all 67 matching-source
Stream B compile records qualified immediately would leave **133 prerequisite
modules plus InstalledOp84 = 134 attempts**, or 137 including the reserved
audits. This alternative is not credited as verified reuse. Both estimates
exceed the fresh 100-attempt budget before step 2 begins.

Step 2 additionally requires actual invocation/exclusion arguments for the
seven inherited complement entries, native conditional success and non-vacuity
for both shapes, and two coverage/minimality results. An initial work breakdown
is 7 exclusion modules (at least 14 shape-specific claims), 2 native-witness
modules (at least 4 success/inhabitance claims), 2 reached-set modules (at least
4 coverage/minimality claims), and 1 comparison/audit module: **at least 12
planned modules and 22 substantive statements**, before the missing reserve,
guard and native-effect transport lemmas. These are planning estimates, not
proofs that those interfaces suffice. A credible attempt estimate cannot be
smaller than those 12 first compiles, and will need elaboration/debugging and
additional transport modules. There is no plausible route within this budget.

Under the user's ninth-round lead note and AGENTS.md security section 7, this
run stops at the feasibility review rather than spending the budget on a
prerequisite prefix or partial reachability wrappers. The requested step 1
cannot be finished within this budget on the verified evidence. No failed
candidate lemma, reservation refusal or transport failure caused this stop.

## Validation and unchanged obligations

All 5,673 effective external objects match h4 before any possible compile.
No Lean/Kani compile or host scope ran; no ID was marked or consumed. IDs
39900–39999, including audit IDs 39997–39999, remain unused. `id-preflight.json`
distinguishes two incidental hex-filename substring hits from attempt records.
The previous run's unlaunched 39406/39476 handling errors are carried forward
in `handling-errors-carried-forward.json`, charged as zero compiles, and not
reused. There are no new handling errors.

V404 OPEN → OPEN; V405 OPEN → OPEN. No complete reached set, universally
excluded actual callback entry, native success witness or minimality theorem
was added. Exact V163/V167 associations and the native non-vacuity obligations
remain as in resume7/native-boundary-review.md. All endpoint premises,
deployment conditions, simulator/observer definitions and the capped three-field
T are unchanged. No source/refinement or release claim is made.

All operations on the host were read-only; resource/axiom compile receipts are
not applicable. No Lean or shipped source, object, key, sibling worktree, shared environment or
launcher was changed. No unchanged proof or release replay was rerun.
