# Shared source preflight and retained cohorts

No shared env-J source was written. The read-only preflight resolves shared
modules through EJR_final-inventory.json and checks the research-HEAD path in
that record, rather than selecting a similarly named file by search.
Rebuild2 evidence was checked for these module names; no override was found.

Two shared sources fail the rebuild-authority byte comparison. Stop these
modules as shared-source targets; do not replace them:

| Module | EJR research-HEAD resolved source SHA256 | Shared source SHA256 |
|---|---|---|
| AspisR1PublicPreparation.Funs | c3dd345a41c971c00dcae53a4799eaeebccfd953abda3ad7390da78a5a07995b | e98bb12315c0da46e34d99c74f41db6b40fa005b023cfd0679423d1452355650 |
| AspisR1PublicPreparation.Types | b45ee7357278642101b81933252e81f5068c937487acfdebb4f82f991c91bb83 | 34d88375248f4a2ca8119a215e4598474c3a095670a6d72ae1c4b3e7d93f4220 |

Their shared source and object hashes exactly match the dictionary branch's
retained formatter262/closure-input.json cohort. Thus focused dictionary
checks can reuse that explicitly pinned historical cohort; they cannot be
called a coherent rebuild-authority release replay. The complete paths, blobs,
revisions, source/object hashes and comparisons are in cache-provenance.json.
No source-level resolution of this disagreement is claimed. The lead must
identify the cohort intended for the full integrated release closure, after
which any required alternate variant belongs in an owned objects directory.

85 objects in the requested union were missing at preflight, including the
39 RemainingCommute231 modules, File/OS-world modules and owned-coefficient
laws. The dependency-first recheck queue contains 91 targets (85 missing plus
six available top-level targets); every fresh object is emitted solely into
/home/dombarker/project-offloads/codex-pv-dict2-20261027/lean-objects/.

Only the available pinned imported objects are reused. Source equality is not
inferred from a module name, and an object differing from an older audit hash
is recorded as such rather than attributed that audit. Focused new #print axioms
results concern the actual input objects fingerprinted by each new submission.

## Owned overlay environment corrections

J54601 failed before elaboration on missing direct-import object resolution.
J54602 exposed an unlisted transitive ExternalTypes object. J54603 exposed
Lean 4.32 .olean.server sidecars; J54604 exposed missing Init.Prelude IR.
Each is charged and retains its exact output/time/input. The final overlay
includes existing available project cache objects plus their server/private
sidecars, IR and ilean inputs. Broken pre-existing cache links are skipped, not
repaired. The overlay links only to retained cache files, with target links
unlinked in the owned tree before every fresh compilation (including sidecars,
IR and ilean); no compiled output is allowed to follow a link to a shared file.
This changes the input search environment of each successor, not a proof.
Source hashes and proof statements are unchanged.
