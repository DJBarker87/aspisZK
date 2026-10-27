import PV_B3_Copy_222_Funs
namespace PV_B3_MultilinearFidelity222
open Aeneas Aeneas.Std Result PV_B3_Copy_222
set_option autoImplicit false
abbrev Q := aspis_core.field.QM31
-- The all-Boolean point has prefix_len=0, exactly one sparse weight and
-- exactly one evaluation iteration. These are concrete runtime checks only.
def seven : Q := {c0 := {a := 7#u32, b := 0#u32}, c1 := {a := 0#u32,b := 0#u32}}
def sevenColumn : Slice Q := ⟨List.replicate 1024 seven, by simp⟩
def limbs (q : Q) : List Nat := [q.c0.a.val,q.c0.b.val,q.c1.a.val,q.c1.b.val]
def run : Result (Option (List Nat)) := do
  let q ← host_multilinear.multilinear_evaluate_qm31 sevenColumn
    (Array.repeat 10#usize aspis_core.field.QM31.ZERO)
  ok (q.map limbs)
#eval run
#print axioms sevenColumn
#print axioms run
end PV_B3_MultilinearFidelity222
