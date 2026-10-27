# Rejected preprocessing experiment

pv12-goto-opt01 exited-6 (wrapper250), invariant violation in reaching_definitions.cpp356, range_end>range_start, during full slicing. No output GOTO model exists; zero verification runs charged. More importantly its log explicitly warns that goto-instrument constant propagation is not expected sound and full slicing may be unsound. Both options are excluded from this task even if the crash could be avoided. The earlier planned property-preservation classification is withdrawn. No source/result is adopted from this pass. Original Kani model remains intact.

Any next experiment must retain the complete original assertions and use only ordinary inlining, not either rejected option. No tool or launcher is patched, no cap/check is changed, and no source helper is replaced by a summary/stub.
