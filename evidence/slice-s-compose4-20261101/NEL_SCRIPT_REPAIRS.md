# Own input/validation repairs

- Bootstrap copy omitted frozen include files; exact 4bb3b3f5 sources restored
  and pinned. K001 is an excluded compiler failure.
- K004/K005 oracle placement/import/visibility errors were repaired in own
  scratch inputs. K006 pre-submission patch failures launched no process and
  were corrected before its one actual compile/proof.
- K036 missing Arbitrary for own local State caused codegen failure. The derive
  was added; original names/properties retained in K039..041. The failure is not
  an interface control.
- L008 numeral binder elaboration, L010 count proof/layout and L014 existential
  binder syntax were repaired; failed attempts stay excluded. L009/L012/L015
  are the successful changed-source attempts.
- A validator refactor omitted the certificate kind when checking shared
  fidelity data. The wrapper was corrected; all underlying gates remain.
- Overlapping local tests wrote a shared log. The unambiguous final run uses
  NEL_TESTS_FINAL.log plus a source-pinned receipt; this is the missing-artifact
  reason for that focused rerun. No Lean/Kani rerun was involved.
- The common inverted-postcondition control gap was disclosed in
  NEL_CONTROL_CORRECTION.md. K060 supplies actual reply corruption; the validator
  now requires both the contract and oracle-corruption controls.

No lead/host reservation, launcher, shim or shared workspace was repaired or
modified. The copied S2W launcher remained byte-identical. Caps never increased.

Archive deviation: the adapted script retained compose3-cache in its destination. Only the newly created NEL_final_objects_20261102 directory was moved to the assigned compose4 cache, after complete file/hash checks; the predecessor addition was removed and original files were not modified. The own script path is corrected. See NEL_ARCHIVE_REPAIR and NEL_CACHE_FINAL.json.
