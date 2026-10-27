# Parser final stage 2

`PFin_Top.deployed` compiles (attempt009, standard axioms). It preserves the
Rc2 root hypotheses, headline, copy/event/protection conclusions, and the SAME
Rc2 result witnesses. Its PFin_Result/PFin_Caller conclusion removes L099's
FirstEntryVerifierConeJoin application guard. No new input premise replaces it.

PFin_Result.strengthen obtains the source getter-selected public from Rc2's
existing base output and uses those selected cuts on the same proof bytes.
PFin_Entry derives a reached run on those source cuts. PFin_Prepared extracts
the F3L 33-row model transcript/input on that run. PFin_Gates derives Aligned,
literal-data read and query decoding. This closes L099 even though the source
getter-selected run need not definitionally be the older existential run in
Rc2. It does NOT yet remove finish guards for the older run.

Ledger delta at this stage: L099 removed, no added assumptions, all other rows
retained. Seven requested gate families: 1 removed, 6 remain. Deduplicated
actual plus non-alias deployment changes from T88/P184 to T88/P183; actual
antecedents T82/P171 to T82/P170 (lead decreases by1). This is an audit count,
not a soundness percentage. The authoritative shared ledger is untouched.

Non-vacuity: the transformation takes an existing Rc2 result and adds no
antecedent. Joint satisfiability of the complete retained Rc2 interface is
NOT established, and its inherited frozen2 raw join is not repaired here.

9/100 Lean invocations, 0/10 Kani. Attempts001/003/007 failed elaboration;
their sorryAx diagnostics are excluded. Successful new theorems use only
propext/Classical.choice/Quot.sound. Caps6G/8G/swap0/tasks64, -M7000,
one scope at a time. No timeout/memory kill or package replay.
