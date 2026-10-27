# Kernel memory review and permanent replacement

082's explicit18-height rewrite proof on concrete nested output definitions
was rejected by the kernel for excessive memory consumption.083 split one
tree and replaced the nested outputs by existential intermediate states, but
its large explicit elimination/rewrite proof still exceeded-M7000. Both
failed sources/diagnostics/time and exact hashes are retained. Neither source
was rerun unchanged or with a larger cap; no source claim receives credit.

Replacement:084 proves HeightTools.compose by generic induction on an abstract
phase predicate and step.085 instantiates a finite PhaseView/step contract for
tree0, reusing every checked native level theorem; the complete height theorem
is one named generic application.085 passes with standard axioms. The generator
now emits this phase-indexed method permanently. Initial (079) and Valid (080)
were independently green before the joins. The next two trees use the same
changed mathematical shape, not the failed explicit proof.

All scopes retain MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64,-M7000.
No OS-level cap increase, swap or unrelated-job termination occurred. Failed
kernel recovery outputs mentioning a newly generated source constant are
rejected diagnostics, never accepted axioms or proof evidence.
