The complete old/new four_dots functions now have an exact paired source kit.
extract-cu-dots.py --check asserts the sole candidate-10 delta is the original
three-line fixed-prefix addition. Both entire functions and the unchanged
field.rs, field/wide_exact.rs and fast_pairing.rs are copied verbatim. These
files are unchanged from candidate 10 through production revision 39c2971dd.
Only a small crate/module boundary is added; no Rust function body is edited.

cu-dots-charon-a successfully extracts both complete functions and all closure
loops, with identical arithmetic callees deliberately opaque for a parametric
comparison. Exit 0, wall 1.604 s, peak RSS 228836 KiB, zero process/cgroup swap.
cu-dots-aeneas-a successfully emits both complete function/loop declarations
using the isolated tested no-branch-join frontend. Exit 0, wall 2.205 s,
peak RSS 135696 KiB, zero process/cgroup swap. Both actual scopes are capped
at memory high/max 6/8 GiB and swap max 0; commands, revision, features, pins
and host observations are in the respective receipts. These are frontend
runs: #print axioms is inapplicable, and no new Lean success is inferred.

The generated FunsExternal_Template.lean is DIAGNOSTIC ONLY. Its axiom
placeholders are not imported or admitted. Shared arithmetic leaves need
explicit universal parameters or already checked concrete definitions, and
core.array.from_fn needs a concrete state-threading interpretation plus its
standard-library source boundary. Treating an arbitrary polymorphic array
constructor as extensional would be unjustified. The emitted old/new closure
carriers also differ (Slice versus Array 608); their source-loop relation must
consume the checked range identities and actual loop bounds.

Next: introduce the shared arithmetic parameters without changing emitted
bodies, implement and check the array-construction relation, and compare the
actual emitted loops/callbacks. Then discharge the whole-function caller
bound using CuSavingsQueryAccess. The complete candidate-10 equivalence and
final soundness/privacy transfers remain OPEN. Production Rust is unchanged.
