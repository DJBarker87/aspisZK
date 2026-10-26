# Rc6 same-witness composition

Base: AspisR1.Rc5_Top.deployed. Derive PFin parser packet and eliminate FirstEntry on the existing cuts; retain Rc5 finish/query reductions. Attach P6 accepted-run refinement on those cuts. Prove reverse transport to Rc5, dictionary compatibility, and retained non-vacuity. Fresh kernel inventories and append-only mechanical ledger recount follow.

Budget: 100 Lean compile attempts including missing dependencies; 10 Kani maximum. No package replay. One 6G/8G/Swap0/64 scope at a time; Lean -j1 -M7000. Reuse coherent SInt2 objects; immutable parser packet cache may supplement it after source/hash verification. No shipped files or ELF rebuild trigger.

Expected delta subject to compilation: L099 actual P; L195–L199 deployment P. The seven SessionAPrepare leaves were already removed on Rc5 and cannot count twice.
