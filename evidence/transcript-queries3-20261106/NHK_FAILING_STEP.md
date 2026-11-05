# Retained failing steps

NHK_K001: stage 1, literal length11 owned canonical22/inactive-zero contract,
assertion `result == expected` where expected is the scalar active-prefix
predicate. CBMC reached its unchanged90s limit; scope receipt is retained.
Tool limit, not a semantic mismatch. No credit and no unchanged retry.
Replacement: smaller slice windows and their explicit frame/concatenation
obligation; other missing lengths are independent and proceed first.

NHK_K002: literal length12, same owned canonical22/inactive-zero contract family, CBMC90s timeout, scope exit1, wall94.828073s, peak6351420KiB,swap0. Excluded; split by native contiguous windows, no unchanged retry.

NHK_K003: literal length13, same owned canonical22/inactive-zero contract family, CBMC90s timeout, scope exit1, wall94.832153s, peak6351540KiB,swap0. Excluded; split by native contiguous windows, no unchanged retry.

NHK_K004: literal length14, same owned canonical22/inactive-zero contract family, CBMC90s timeout, scope exit1, wall94.658210s, peak6351600KiB,swap0. Excluded; split by native contiguous windows, no unchanged retry.

NHK_K005: literal length15, same owned canonical22/inactive-zero contract family, CBMC90s timeout, scope exit1, wall95.536667s, peak6348228KiB,swap0. Excluded; split by native contiguous windows, no unchanged retry.

NHK_K008/K009: length20 positive passes, matched inverted-result control reaches90s solver limit. No credit from the unpaired pass. Replacement is the native window split; not a semantic mismatch.

NHK_K010/K011: length21 positive passes, inverted-result control times out90s; no credit. The old positive is retained without an unchanged replay.

NHK_L001: owned proof used unavailable decide_or and positional List.take_add arguments; elaboration failed, sorryAx outputs excluded. L002 corrects Bool cases and implicit list parameters; all three window laws pass with standard axioms.
NHK_L003: owned trace induction omitted the dependent continuation argument to IH. L004 applies IH to that continuation; append passes with standard axioms. These were elaboration errors, not native/model mismatches.

NHK_K012/K013: arbitrary-offset native full-window membership versus native
prefix8/suffix windows, lengths11/12 respectively, no contract snapshots.
Both reach the unchanged90s CBMC limit. No value law or split credit. The
remaining full-window queue was stopped locally; K013 finished once without
interruption/resubmission. Smaller scalar windows are checked first.

NHK_L006/L007: owned effect-join elaboration did not identify the generated
pair-pattern continuation with the explicit projection continuation. L008
adds the explicit equality but has an extra completed-goal tactic and a
multiline tactic layout error. L009 removes the extra tactics, parenthesizes
the continuation application and accepts all eight roots with standard
axioms. No failed root/receipt is promoted or used as evidence.

NHK_K016/K017: arbitrary-offset width3/4 scalar membership window gates
time out90s; no credit. Width1 K014/K015 has a matched pass/control. The next
shape fixes the caller's actual prefix start, retains both reference windows
and broadens inputs to all u32 arrays/candidates; there are no contract
array snapshots, aggregate any return or arbitrary-offset pointer selectors.

NHK_L012: native-word association/source were accepted but the domain
corollary used the wrong validState namespace and lacked the explicit
NHB_Canonical import. L013 corrects only those owned inputs and passes all
three roots with standard axioms. NHK_L017 used reserved prefix as a
theorem identifier; L018 uses prefix_transport. No failed receipt is credit.
