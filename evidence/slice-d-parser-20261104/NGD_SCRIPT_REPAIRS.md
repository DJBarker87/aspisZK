# Own-script repairs and preserved checks

No reservation, launcher, shim, monitor or shared workspace infrastructure was
edited. All changes below are confined to NGD runner/validator inputs.

- L001: own dotted module source path was corrected to a slash path before L002;
  the prelaunch error is charged and not presented as a host result.
- Full Error extraction caused an instance-name collision; only our generated
  discriminator name/annotation was normalized to ImportUnionNamedDiscriminant.
  NGD_ERROR_DISCRIMINANT.diff preserves the change, original extraction snapshots
  remain, and Types/Funs/dependent modules were recompiled before use.
- Own audit runner supports a distinct Stage2 driver/output directory, pins its
  combined import, and reads the original same-driver raw walker. Final batch
  sources identify L069 rather than the old slot batch L019. Original slot audit
  remains intact; no check was removed.
- Expected imports for the new union are derived from committed sources and the
  inherited NFX baseline; new baseline additions are separately pinned. Actual
  scan output is not used to manufacture an expected table.
- Final local validator initially hardcoded 493 source files. Scope snapshots
  actually pin 499/500 files (498 baseline including root Cargo files, plus own
  sidecars). Replaced that mistaken count with exact equality to EACH receipt's
  committed NGD_SOURCE_PINS.json length. Every individual source hash, graph,
  lock and source-check error list is still checked. This is stricter than a
  minimum count; no native run or verdict was changed.
- Token erasure explicitly normalizes Rust's struct-field shorthand and optional
  trailing commas. It checks the two frozen caller bodies and exact assignment;
  three corruptions must fail. This is syntax provenance only, never substituted
  for the open semantic transport.

NGD_campaign_validate.py is additive to NGD_validate.py and NGD_slot_validate.py.
It rejects invented extra closures and retains all failures and open edges.
