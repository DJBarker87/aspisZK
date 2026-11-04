# Validation findings

Inherited NEU test run: 24/25 passed; `NEU_transport_tests.Transport.test_identical_inherited_inputs` fails on the committed NEU checkpoint because it still asserts NEU's entire overlay equals NEQ's older overlay byte-for-byte. NEU added four admitted rows, so this historical setup test is stale. The original test is retained unchanged; no passing total is claimed. NEX_BASELINE_VALIDATION independently reproduced 72/97 and 2/7 roots under all inherited gates. New transport tests compare NEX's inherited overlay against the actual NEU baseline and validate each additional certificate separately.

NEX_L004/L005 are excluded elaboration failures in new symbolic range laws. The goals needed explicit length numerals and reduction of only small constant min/sub arithmetic; changed-source L006 passed with standard axioms. `sorryAx` appearing in failed elaboration audits is excluded, not admitted. No source contains sorry/admit/axiom/native_decide.

NEX_K002 is excluded: outer timeout180s, cgroup memory peak6692216832 bytes, process time RSS100812KiB does not represent aggregate child memory. Replaced by separate returned-field windows K003 onward, with no cap or timeout increase. K003 passed and K004..007 detect corrupt value, different allocation, wrong child slice, and wrong reply.
