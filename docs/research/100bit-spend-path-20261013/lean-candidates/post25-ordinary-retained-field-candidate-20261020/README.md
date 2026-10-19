# Post-25 ordinary sample retained-field candidate

This focused packet proves a candidate-only representation join. The fresh
extracted `ordinary_sample` wrapper returns a value, and the retained-field
interpretation of that value is the base-P rank of the 32-byte block reduced
modulo P^8. The proof goes through the actual extracted `decode8` body and the
existing `digitsField`/`fieldRank` model.

It does not establish production equivalence, gamma sampling, or a sampler
density/distribution theorem. Exact source, object, import, timing, and axiom
pins are in `manifest.json`; native objects are excluded.
