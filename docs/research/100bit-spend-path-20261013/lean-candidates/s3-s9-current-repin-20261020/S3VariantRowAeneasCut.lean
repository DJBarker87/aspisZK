import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error

/-! Axiom-free source cut for the non-D (including S2) arm of the exact
extracted `Variant::row` loop. The D-only coefficient-table import and the
unrelated `from_fn` template are intentionally absent. -/
namespace AspisR1.S3VariantRowAeneasCut

@[global_simps, irreducible]
def tau : Array Std.Usize 5#usize :=
  Array.make 5#usize [3#usize, 4#usize, 2#usize, 0#usize, 1#usize]

@[rust_loop_body]
def row_loop_body (j : Std.Usize)
    (iter : core.ops.range.Range Std.Usize) (out : Std.Usize) :
    Result (ControlFlow ((core.ops.range.Range Std.Usize) × Std.Usize) Std.Usize) := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done out)
  | some d =>
    let i ← 2#usize * d
    let i1 ← j >>> i
    let i2 ← lift (i1 &&& 3#usize)
    let i3 ← Array.index_usize tau d
    let i4 ← 2#usize * i3
    let i5 ← i2 <<< i4
    let out1 ← lift (out ||| i5)
    ok (cont (iter1, out1))

@[rust_loop]
def row_loop (iter : core.ops.range.Range Std.Usize)
    (j : Std.Usize) (out : Std.Usize) : Result Std.Usize :=
  loop (fun (iter1, out1) => row_loop_body j iter1 out1) (iter, out)

def s2_row_result (j : Std.Usize) : Result Std.Usize :=
  row_loop { start := 0#usize, «end» := 5#usize } j 0#usize

#print axioms row_loop_body
#print axioms row_loop
#print axioms s2_row_result

end AspisR1.S3VariantRowAeneasCut
