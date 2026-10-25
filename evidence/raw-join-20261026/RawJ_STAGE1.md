# Account query envelope and collision arithmetic

Checked RawJ_AccountBudget.budget: complete GExq_AccountExperiment.program,
fixed before H, has all-world log length <= Q0+Q1+1921. Preprocessing and
adaptive second choice retain explicit uniform Q0/Q1 premises (the latter
ranges over original first input, actual saved bytes, post heap and final
allocator state). All outcomes, including rejected prefixes, are covered.
This is a fresh structural proof through the original owned caller, all
polymorphic child calls, reserve/copy/cleanup wrappers, and adaptive composition.
The inner 1921 number was not assumed as a bound on the containing program.

RawJ_CollisionBudget.replay_collision charges all1040 canonical replay calls:
6*(Q0+Q1+2961)^2/2^256. RawJ_Numeric.account_replay checks the binary denominator.
RawJ_Numeric.zero_queries and margin_positive check a conservative EndP sum
retaining its original 1161 frozen collision term and both abort terms.
Exact remaining margin at Q0+Q1=0:
2^-108 - 6*(1161^2+2961^2)/2^256 - 2^-126 - 2^-454 >0.
No target relaxation or shortfall. This arithmetic does not establish an
account-to-headline event association or L157.

Ledger delta: NONE. L157/L182 remain OPEN; L159 excluded. No security/trust
premise removed or added. The account all-world query bound is now derived;
physical SDK/helper refinements remain inherited. No raw Port1 log equality.

25 charged attempts (24 actual invocations, one own missing-prerequisite
prelaunch007). Attempt006 was configured before007 but ran after008; each
number identifies its unique invocation. No timeout or memory kill. Successful
current modules have only propext/Classical.choice/Quot.sound; failed recovery
sorryAx output is excluded. Exact command/source/deps/revision/status/wall/RSS/
swap/axioms are in each receipt. No package replay, Rust, Kani or ELF build.
Next: response-derived full records on the inherited same cuts and original
C1/C2 occurrences, then restricted start charge and strict raw join.
