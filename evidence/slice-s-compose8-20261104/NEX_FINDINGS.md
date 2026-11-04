# Validation findings

Inherited NEU test run: 24/25 passed; `NEU_transport_tests.Transport.test_identical_inherited_inputs` fails on the committed NEU checkpoint because it still asserts NEU's entire overlay equals NEQ's older overlay byte-for-byte. NEU added four admitted rows, so this historical setup test is stale. The original test is retained unchanged; no passing total is claimed. NEX_BASELINE_VALIDATION independently reproduced 72/97 and 2/7 roots under all inherited gates. New transport tests compare NEX's inherited overlay against the actual NEU baseline and validate each additional certificate separately.

NEX_L004/L005 are excluded elaboration failures in new symbolic range laws. The goals needed explicit length numerals and reduction of only small constant min/sub arithmetic; changed-source L006 passed with standard axioms. `sorryAx` appearing in failed elaboration audits is excluded, not admitted. No source contains sorry/admit/axiom/native_decide.

NEX_K002 is excluded: outer timeout180s, cgroup memory peak6692216832 bytes, process time RSS100812KiB does not represent aggregate child memory. Replaced by separate returned-field windows K003 onward, with no cap or timeout increase. K003 passed and K004..007 detect corrupt value, different allocation, wrong child slice, and wrong reply.

L017/L018 excluded: a freshly cloned, twenty-one-call emitted decoder continuation hit Lean recursion depth. No option was raised. L019/L020 reuse the already factored NED_SubtreeComposition and S6NativeSnapshotDecoderFactored laws, with standard axioms. The new wrappers add state/trace checks; they do not re-prove the old parser.

Full-error-interface finding: K003..035 common and K060..067 afterdecode use Result<Digest,()> at the digest oracle. Ruling (y) requires the full AtomicStatementError return type; these runs receive NO composition credit. Exact closure and boxed wrapper checks use full types and are unaffected. Replacements enumerate all seven AtomicStatementError variants. K067 wrong-root-reply control passed because its slot0 property observes the index, not the root; it is an uninformative control, not a Kani defect. Its replacement keeps the original harness name and selects the actually corrupted root field (slot1).

Final checkpoint:82/97 composed rows and2/7 roots; target not yet established.
The early common and raw-afterstate Unit-error oracle windows are excluded,
then replaced by full AtomicStatementError checks before any new closure.
No previously admitted row relied on the excluded windows. See
NEX_CREDIT_EXCLUSIONS.json for every excluded attempt.

K132 is an excluded own projection type error (u32 withdrawal amount vs u64
observation); the repaired exact lossless cast is in K133's snapshot. K133's
26-field terminal-parent check timed out at the unchanged90s solver limit.
No unchanged retry or timeout increase occurred. Split output projections and
validator continuations before a future attempt; L035 already supplies complete
record extensionality. This is not evidence the terminal theorem is false.

K134 failed fully-qualified harness selection before solving. The owned campaign
removed only an incorrect crate qualification; the original module/harness and
property remain unchanged. K135/136,137/138,139/140 are matched result-encoder
windows; they provide no full parent, child/domain or root credit.

The final new bridge mutation suite passes5 tests. The retained inherited suite
has one stale whole-overlay equality assertion against the previous checkpoint;
its earlier24-pass/1-fail result remains visible. Do not convert it into a pass
by weakening a gate. Existing NEX mutations and final replay have separate logs.

Ruling(ab) resolves policy for return-data by ADDING runtime trust, with zero
CLOSED native uses here. L039 explicitly retains BindingBridge/EncoderBridge;
the modeled trace law does not establish native platform readback or justify
op53 Unit erasure. No private/static/function-pointer suspended pass is credited.
