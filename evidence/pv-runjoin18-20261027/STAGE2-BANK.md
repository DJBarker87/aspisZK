# Bank validation helpers; concrete 57-block certificates still open

Accepted source lemmas: BankRounds18.rounds and .padding (51087), BankInitial18.initial (51089), BankAbsorb18.absorb (51090), BankBlock18.block (51093), BankReads18.index_value/.read (51094), BankAggregate18.loop/.rows (51098). Each has a standard-only axioms report and zero swap; exact wall/RSS/revision/source/dependencies are in its receipt and receipt-index.tsv.

The proofs are symbolic inductions over lanes, local rounds, padding rows, and blocks. BankReads proves actual Vec reads for every bounded block/row/lane from an arbitrary flat table after the source columns construction. BankBlock composes initialization, absorption, eleven checked pair transitions/read equalities, and three padding-row read equalities. BankAggregate composes the 57 per-block successes with actual late/stable selection (34≤block<54). Its `blocks` premise is NOT discharged. No whole bank is evaluated, no generic hypothesis is represented as a fixture fact, and no 57-block certificate is claimed.

Remaining: concrete source CopyRecords.banks materialization, actual per-block round-pair and row-read certificates for both fixture banks. Numeric node certificates alone do not prove this validator: its separate apply_round_by_index/evaluate_trace_round_pair path and actual bank rows must be identified. All conditional premises are P proof obligations; none is placed in T.

LateCall18.transfer/.withdrawal (51099) composes CopyRecords.output_pair into the actual late_append call. This remains a compiler subexpression, not the compiler return equation, actual selected-i transition, deployed public binding, or non-vacuity witness.

V152–V154 compile_call is further reduced by full late_append and these conditional helpers, but all whole rows remain retained. V038/V045/V047 are unchanged. Endpoint premises removed/added/weakened 0/0/0. Constructed P={source public binding,trace}; deployed P OPEN; records 2/8/6. T=entropy_law,entropy_kernel,observation.
