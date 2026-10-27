# Same-environment obstruction: actual producer and LPq consumer

LPs_L098, exit1, fails before elaborating any declaration:

    import LPl_Kit_TypesExternal failed, environment already contains
    'core.slice.iter.Windows.noConfusion' from XRn_Join_TypesExternal

The two TypesExternal source files are byte-identical, but are distinct Lean
module owners for the same root declarations. The import chain LPq→XRn and
LPl_Check→LPl_Kit_TypesExternal cannot coexist. Separate compilation of both
is not a checked join. The original LPl_Coimport test only imported
AspisR1FinishRelationCurrent.Types, not the LPq/XRn owner.

No original module, shared object or launcher was modified. The rejected join
is preserved in L098's exact source snapshot. Rule4 stops the ill-formed
same-environment item. Remaining native check/expand facts are compiled in
the producer environment and LPr→LPq nominal application in the consumer
environment. They cannot be credited as prepared_claim closure.

Next deliverable: lead-owned canonical TypesExternal ownership/import
normalization and coherent rebuild of affected downstream modules; then import
the producer and consumer together and connect the definitionally matching
word/byte predicates. Do not shadow an old module with changed bytes, relabel
an object, or infer co-import success from equal source/object hashes.
