# Stage 4: first complete raw P6 equality

Checked Kani gates (NOT complete external/leading/full values yet):
- K006 raw component2, source-order aligned owned reference, kernel-derived
  redundant local-row bounds: exit0,10.108814770996105s,293196KiB,swap0;
  0/966 failed,1/1 domain cover reached.
- K007 COMPLETE four raw outputs: exit0,17.995636205014307s,294508KiB,swap0;
  0/971 failed,1/1 domain cover reached.
Both compare the original native helper with the owned safe reference on the
SAME arbitrary canonical4x4 limbs. Native operations and all runtime safety
checks remain present;no stubs,no output hypothesis. Assertion-reachability
DIAGNOSTICS disabled;explicit domain covers retained. All outputs are scalar
compares,avoiding unrelated memcmp. Reference operation/constructor order was
aligned to source,eliminating the expensive divergent formulas of K003–005.
K005 had timed out120.00253861001693s;its source/receipt is retained.

Lean012 rebuilt only the missing unchanged pure PoseidonExternalPackedAlgebra
module,not the legacy native packed-proof chain. No pre-existing source or
object was overwritten.013 checks the owned raw reference's field closed form,
row bounds and output range by importing that algebra.014–017 check exact
source-order intermediate arithmetic bounds per component.018 checks the
original final constant4x16 table reads,bounds,and literal R0P meaning.
All printed axioms are subsets of propext/Classical.choice/Quot.sound.
Per-attempt receipts include exact source/dependency pins,revision,status,
wall,RSS,swap,cgroup and complete prints. No package replay/cap increase.

Budget:18/100 Lean,8/20 Kani (K008 complete external in progress).
No deployed premise removed,top/dictionary/game/fixture changed,shipped-file
edit or ELF rebuild trigger. Whole external/leading/full P6 and their complete
Lean source-to-closed-form installation still required.
