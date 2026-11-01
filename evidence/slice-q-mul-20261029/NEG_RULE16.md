# Rule 16 resumption

Prior usage: 12 Kani, 40 Lean, 20 extraction receipts. Remaining: 63 Kani (60-12+15), 20 Lean, zero extraction. Lean attempt identifiers have gaps; their upper identifier is not budget usage. Runner maximum identifier adjusted to 64 accordingly, Kani to 75. Actual receipt counts remain authoritative.

SUSPENDED: NEG_K003 row_step_check and NEG_K009 term_check, plus their controls K004/K010. Both wrote LOG statics. K001/K002 copy_check and K005/K006 flush_step_check do not reach product or LOG writes. K007/K008/K011/K012 use exact KMX ptr controls with no writable static. These remain subject to source audit.

The replacement retains original names and assertions, passes local log records by &mut, and removes all static state in the scratch harness modules. Historical source snapshots are retained as evidence only and are never runnable inputs. No shipped file changes.

Restored step checks: NEG_K013/K014 re-establish verifier::NEG_step::row_step_check (0/57 failed; control 1/57 failed at intended assertion); NEG_K015/K016 re-establish fast_dots::NEG_dot_step::term_check (0/208 failed; control 1/208 failed at intended assertion). All use exact KMX patch, frozen resolved graph and unchanged lock, deployed features, local &mut log records. Old passes remain historical suspended receipts; only replacement pairs are cited. These are surrogate product-abstracted source-step checks, not actual full-function Kani passes.

Own gate now rejects any static declaration in both own harnesses and KMX sources before each future Kani run (stricter than rule 16); no shared launcher changed. NEG_L044 was interrupted before a receipt existed: read-only recovery returned no files. It is unresolved and is not resubmitted unchanged. Count conservatively as one possible extra Lean attempt, leaving at most 19 Lean runs at resumption.

Final accounting follows the user's explicit ATTEMPTS-file rule: 60 Lean receipts, 20 extraction receipts, 24 Kani receipts, five native receipts. L044 remains prepared/unresolved with no executed receipt; it was not resubmitted. The earlier conservative remaining-19 estimate was precautionary, not an extra receipt. Thus 51 Kani remain and neither Lean nor extraction capacity remains.

K021/K022 additionally refresh copy_check; K023/K024 refresh flush_step_check after complete removal of all static declarations from both harness modules. Original K003/K009 remain suspended historical artifacts; replacement pairs alone support current step claims. No Option<fn> or function-pointer-dependent pass is used.
