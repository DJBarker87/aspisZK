# Stage 6 — complete native body query bounds

Checked symbolic resource bounds include all response paths and rejection:
leaf1; P6node1; rows≤fuel; reached level≤16; height traversal≤16*height;
P6 verification≤288; native outer step≤288; fuel loop≤288*fuel;
each tree≤3744; three-tree batch≤11232; writer3; reader3;
complete TX1≤11350; complete TX2≤11235. Preparation115 is included in TX1.
All counts retain repeated reads. Domain preservation between P6 levels is
DERIVED through the existing source theorem in the ideal dictionary, not
assumed at the top. The native syscall is still partial.

These bounds are intentionally conservative: the outer-loop proof charges
288 at each iteration although leaf continuations cost1 and only the final
iteration verifies. No source-exact tightness or new 100-bit conclusion is
claimed. Combined native envelope22585 exceeds1161 by21424. This excess must
be included in any derived collision budget; the old1161 headline cannot be
reused with these bounds. The (Q+34) start charge is NOT rederived here.

042 failed because overloaded bind did not elaborate to the explicit Code
constructor;044 uses explicit bind.066 failed on passing a variable to the
numeral-only proof tactic;068 uses then_count directly.067 was an accidentally
early dependent prelaunch, charged and documented. All current bound modules
have exact successful receipts and standard-only axioms. No timeout, memory
kill, cap raise, package replay or unchanged regression. Budgets count every
attempt including prelaunches and unchanged dependency builds.
