# NJH findings

NJH-F1: NIV_L022 has no emitted observer declaration. Its committed NHR_DECLARATIONS.json and raw/NIV_entry/Funs.lean contain only entry/process and trait support. AdapterRwModel.lean:648 does contain a canonical emitted observer body, returning `ok none`. NJH_Observer proves that existing body without a native Option<fn> assertion. It must not be attributed to NIV_L022. No extraction has yet been spent, and no row promotion is claimed from an incorrect provenance statement.

Owned runner repair: derive LEAN_PATH directly from NJD_L033 and prepend owned copied seed/objects, preserving all inherited dependency locations. No shared infrastructure changed.
