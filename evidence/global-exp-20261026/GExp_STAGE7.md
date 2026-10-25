# Stage 7 — fixed-before-H adaptive source experiment and collision accounting

GExp_Experiment.program is defined without H. It quantifies an arbitrary
oracle adversary producing TX1 input, then executes full TX1. Only successful
TX1 enters the adaptive oracle program chooseSecond(input,actual saved CP),
then full TX2. Failed/rejected/diverging first results retain their source
prefix and skip the entire second-submission continuation. Earlier campaigns
may be inside adversary/chooseSecond and are charged by their query budgets;
this does not prove native campaign association or impose free retries.

GExp_GlobalBudget.budget (075) proves log length≤Q0+Q1+22585 for every H,
including rejection. The two adversary programs are fixed before H and have
explicit uniform query-count hypotheses. GExp_CollisionBudget (080) derives
first-read≤Q0+Q1+22585 and appends all1040 canonical replay queries, obtaining

    6*(Q0+Q1+23625)^2 / 2^256.

This is an explicit conservative collision bound, NOT a replacement release
contract. Relative to1161 the native envelope excess is21424; appended replay
cost is1040. The restricted (Q+34)*B start-charge argument and the canonical
accepted-log transport remain unproved for this native source experiment.
No 100-bit conclusion or silent constant substitution is made.

GExp_PartialCount (077) proves native attempted-read length is at most the
ideal response-driven execution length under existing P1/partial RuntimeSyscall,
including a failing/diverging syscall itself. It assumes neither native success
nor total syscall success. This connects the all-H bounds to native rejected
prefixes for the reified bodies. No global source/native Runtime equality.

072 failed on Lean's reserved prefix identifier;074 corrects it.073 was an
accidentally early dependent prelaunch, conservatively charged.076 needed
symbolic length_nil simplification, fixed077.078/079 fixed missing namespace
and explicit inclusion of section hypotheses in080. All current audited
results use standard axioms only. No timeout/kill/cap increase or package replay.
