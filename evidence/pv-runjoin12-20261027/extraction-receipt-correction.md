# Extraction receipt classification

The inherited sampling wrapper initially labelled both extraction receipts as Kani/Poseidon. The retained local receipts now carry the actual extraction phase and N/A axioms. Raw scope logs preserve the original output; commands, timings and resource values are unchanged.

Attempt charon-01 was refused by reservation (zero scope). charon-02 passed reservation but stopped before any scope because the historical Charon binary path no longer exists. charon-03 uses the retained s5 Charon binary, hash pinned in its plan; no extractor infrastructure was built or edited. Aeneas candidate-007 is the pinned rng extractor.
