import FJb_TailCell
set_option autoImplicit false
namespace AspisR1.FJe_PackedTableRead
open Aeneas Aeneas.Std Result
open FJb_TailCell (cell)
theorem read0 {T : Type} (a : Array T 4#usize) :
    Array.index_usize a 0#usize=ok (cell a (0 : Fin 4)) :=
  RawPoseidonExternalRowReads.array_index_usize_ok a 0#usize (by decide)
theorem read1 {T : Type} (a : Array T 4#usize) :
    Array.index_usize a 1#usize=ok (cell a (1 : Fin 4)) :=
  RawPoseidonExternalRowReads.array_index_usize_ok a 1#usize (by decide)
theorem read2 {T : Type} (a : Array T 4#usize) :
    Array.index_usize a 2#usize=ok (cell a (2 : Fin 4)) :=
  RawPoseidonExternalRowReads.array_index_usize_ok a 2#usize (by decide)
theorem read3 {T : Type} (a : Array T 4#usize) :
    Array.index_usize a 3#usize=ok (cell a (3 : Fin 4)) :=
  RawPoseidonExternalRowReads.array_index_usize_ok a 3#usize (by decide)
#print axioms read0
#print axioms read1
#print axioms read2
#print axioms read3
end AspisR1.FJe_PackedTableRead
