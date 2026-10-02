# R347 instantiated-name preflight

Read-only source inventory for the output-type name collision question. It copies complete source files and line-numbered excerpts from the R312 Aeneas source tree and the pinned Charon source tree under `ZK-v5-formal/toolchains/charon`. No LLBC, Aeneas, or Charon sources were changed; no naming patch or rule was selected.

Relevant source facts recorded in the excerpts:

- Charon models `PeInstantiated` as a path element containing a generic-argument binder. `match_name_with_generics` strips a trailing `PeInstantiated` element and maps instantiated generics back to the original item for logical name matching.
- Charon pattern generation emits no pattern element for `PeInstantiated` (`[]`), with an accompanying comment that monomorphized elements are skipped in patterns.
- Aeneas `name_to_simple_name` converts `name_to_pattern` into an extraction-name string list. `TranslateCore.name_to_simple_name` obtains a Charon matcher context and delegates to that helper. Aeneas also has `strip_target_or_instantiated_suffix`, which removes trailing `PeTarget` or `PeInstantiated` elements.
- Charon's `PrintFmt` has a separate pretty-printing branch for `PeInstantiated` that renders generic arguments in angle brackets.

These are source-code observations, not an analysis of every output-type naming call site and not a selected collision repair. The R312 Aeneas source's `src/charon` symlink target is absent in the copied R312 directory, so the package linkage used by the prior R312 binary is not established by this inventory. The Charon excerpts come from the pinned project Charon repository at revision `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`; the R312 Aeneas source excerpts are directly from the R312 candidate source tree. File hashes are in `source-hashes.json` and `SHA256SUMS`.
