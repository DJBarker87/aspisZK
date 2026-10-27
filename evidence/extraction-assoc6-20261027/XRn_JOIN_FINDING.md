# Cohort co-import gate

L072 and L073 never invoked Lean: direct-import preflight rejected first the
raw unselected name AspisR1Stage2.Funs, then the unavailable S7OwnedP6QueryRead.
No launcher/infrastructure was changed. The selected actual query reader is
Port5Q1_GeometryBinding.forQuery, installed by Port5Q1_QueryPorts and
IDb_Components; it uses wrapping subtraction. Emitted for_query uses checked
subtraction, so equality is requested on the reached start<=index domain, not
asserted universally. The current cohort geometry already has line_z.

L074 reached Lean but importing the selected geometry cohort failed:
`import AspisR72Sampler.Types failed, environment already contains
'instDiscriminantCirclePointErrorIsize' from XRk_Types`.
This is a genuine co-import obstruction, not an arithmetic proof failure.
No source or object of the existing XRk modules is overwritten.

New XRn_Join_ modules reproduce the 17 checked release-kit files with ONLY:
1. the mechanically uniform XRk_ -> XRn_Join_ module/declaration prefix;
2. Types imports the already pinned ImportUnionNamedDiscriminant adapter and
   uses import_union_discriminant in place of discriminant.
The existing adapter preserves type/tags/readers and qualifies only generated
instance names. No native/extracted body logic, boundary model or type field
changes. All source hashes and attribute replacement counts are retained in
XRn_join_plan.json / XRn_join_transform.json. No new trust, P6 discharge,
source-to-ELF claim or root premise removal is inferred from this repair.

The new kit is used only by new XRn_ consumer modules, to allow proof of the
actual cohort/emitted equations. Existing checked XRn carrier/transcript results
retain their exact original imports and are not silently reassigned to new types.

L076 diagnosed the exact cached adapter syntax: the coherent workspace selects
the original closed-isize adapter (object SHA256
067118f9e821fb4084c22acb15ea80c66f33f26f97ad6246a91910ba3b7098c0),
whose attribute takes no arguments, not the later repository adapter accepting
`isize` tokens. All twelve affected enums are closed isize enums without explicit
tags. The transform now uses that selected adapter's exact argument-free syntax.
The selected adapter still calls the pinned generator with Isize/none and names
the instance by its enum. No alternate adapter object or library path is used.
