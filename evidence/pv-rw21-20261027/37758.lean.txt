import R1Z.ProverRw21FlatOutput
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21FlatLimbs
open Aeneas Aeneas.Std Result ProverRw21ArrayRead ProverRw21FlatOutput

theorem word0 (x : W) : Array.index_usize (words x) 0#usize=ok x.c0.c0.a :=
  exact_read (words x) 0#usize (by decide)

theorem word1 (x : W) : Array.index_usize (words x) 1#usize=ok x.c0.c0.b :=
  exact_read (words x) 1#usize (by decide)

theorem word2 (x : W) : Array.index_usize (words x) 2#usize=ok x.c0.c1.a :=
  exact_read (words x) 2#usize (by decide)

theorem word3 (x : W) : Array.index_usize (words x) 3#usize=ok x.c0.c1.b :=
  exact_read (words x) 3#usize (by decide)

theorem word4 (x : W) : Array.index_usize (words x) 4#usize=ok x.c1.c0.a :=
  exact_read (words x) 4#usize (by decide)

theorem word5 (x : W) : Array.index_usize (words x) 5#usize=ok x.c1.c0.b :=
  exact_read (words x) 5#usize (by decide)

theorem word6 (x : W) : Array.index_usize (words x) 6#usize=ok x.c1.c1.a :=
  exact_read (words x) 6#usize (by decide)

theorem word7 (x : W) : Array.index_usize (words x) 7#usize=ok x.c1.c1.b :=
  exact_read (words x) 7#usize (by decide)

#print axioms word0
#print axioms word1
#print axioms word2
#print axioms word3
#print axioms word4
#print axioms word5
#print axioms word6
#print axioms word7
end R1Z.ProverRw21FlatLimbs
