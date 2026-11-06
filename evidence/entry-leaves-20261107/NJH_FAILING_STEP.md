# NJH findings

NJH-F1: NIV_L022 has no emitted observer declaration. Its committed NHR_DECLARATIONS.json and raw/NIV_entry/Funs.lean contain only entry/process and trait support. AdapterRwModel.lean:648 does contain a canonical emitted observer body, returning `ok none`. NJH_Observer proves that existing body without a native Option<fn> assertion. It must not be attributed to NIV_L022. No extraction has yet been spent, and no row promotion is claimed from an incorrect provenance statement.

Owned runner repair: derive LEAN_PATH directly from NJD_L033 and prepend owned copied seed/objects, preserving all inherited dependency locations. No shared infrastructure changed.

NJH_K001: own wrapper used the AccountInfo lifetime for shared Ref's inner slice; actual SDK elision returns the shorter self-borrow lifetime. K002 repaired that signature without changing the property.
NJH_K002: contract's implicit empty modifies set rejected the genuine RefCell counter write in core::mem::replace::<isize>; this was a frame failure, not an unsupported-function verdict. K003 declared the whole selected RefCell, but used raw-pointer modifies syntax rejected by Kani. K004 uses the accepted reference syntax `&*a.data`, passes, and K005 fails the inverted postcondition. K006 exclusive positive passes and K007 inverted control fails. These remain restricted fresh one-byte wrapper preflights, not actual SDK function contracts or full ABI laws.
L006 failed on a tiny scalar-zero simplification; L008 changed those two proofs to definitional equality. No failed-draft axiom output is admitted.
L008/L009 overlapped K001 under the JOB's explicit two-scope allowance; all scopes separately admitted and capped. Subsequent work uses one scope at a time as stated in the early handoff.
