# NKO failing steps

K001: input harness called nonexistent QM31::new (E0599); no verification ran. Fixed to the actual public raw-word constructors, preserving arbitrary words. K002 is the corrected source, same harness name and property. No timed-out shape retried.

K002: CBMC 90s timeout on inactive payload plus arbitrary whole-proof byte-frame observation (57607-way index). RETIRED. K003 removes that independent whole-proof frame mux; C03 payload/result only, frame remains an explicit separate obligation. Same harness name retained. No cap/timeout increase.

L004: PSem_Slices selects an incompatible historical Phase owner in the combined cohort. Removed that extra import; C03 now proves the concrete range directly over the already loaded pinned Aeneas index definition. This is an own-source import correction, not a shared-cache repair.
