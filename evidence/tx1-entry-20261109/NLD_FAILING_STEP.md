# NLD failure and gap register

Target not yet established. Failed drafts are not admitted objects; their
printed sorryAx is a Lean diagnostic for unfinished failed declarations, not
an accepted theorem. Only successful current-source objects enter the gate.

* L003: missing Aeneas.Std open and the nil-case binder name in the new fold
  algebra. L004 repairs both; exact post-states on fail/div are retained.
* L005: `public` is reserved in pinned Lean; use semantic as the binder.
* L006/L007/L010: error-mapper projection did not expose the nominal
  BuiltinFnOnce.call_once term to generalize. L011 uses that exact callable in
  the source action and its proof. It preserves all mapper fail/div arms.
* L008: structural induction for Program.step has both a continuation-state
  binder and an independent initial-state binder. L009 supplies both; no
  statement or cut premise was weakened.
* L015: run's two-argument projection needs its own conditional-distribution
  lemma; apply_ite alone does not match. L016 uses the proved run_if lemma.
* L018: opening AdapterRw from inside AspisR1 selected the outer runtime
  namespace. Explicit _root_.AdapterRw fixes access to the canonical emission.
* L019/L022: stage1 source-trace erasure still needed congruence/projection
  through full control-flow continuations. Draft and replacement retained.
* L020: `continue` is reserved; the new projection theorem uses advance.
  L021 passes without changing its complete Continue/Break statement.

No timeout, memory kill or semantic native finding has occurred. No native
run, new extraction, shipped-file change, cap increase or unchanged failed
resource-shape rerun has occurred.

The substantive OPEN step is native, not this source-erasure algebra: there
is no NLD frozen first_decoded parent cut with full owned result, nested
ordered effects, accounts/heap/allocator frame and exact 094 packet parameter.
For stage1 the inherited SDK full-carrier law is also missing (NJN_CUTS).
Generic source dictionaries, child Result equations and source heap identities
are explicitly excluded from root hypotheses by (aq)(2). They cannot fill it.

L023: fully qualified NLD_SourceTrace.bind_congr removes an accidental open-
namespace resolution at the source erasure step. Complete stage1_owned
source erasure passes, including every rejecting branch; no statement was
restricted. erase_control was not needed by that final proof, as reported by
the Lean unused-simp diagnostic. Its separately compiled statement is valid.
