import R1Z.ProverRw21VecAppend
import R1Z.ProverRw21FlatSourceLaw
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21EncodedStep
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
abbrev W := ProverRw21FlatOutput.W
variable [ExternalTypes]

@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op51 := ProverRwP6FlatSource.wide_bytes_flat}

def cell (values : Slice W) (i : Usize) (h : i.val<values.val.length) : W :=
  values.val[i.val]'h

theorem read (values : Slice W) (i : Usize) (h : i.val<values.val.length) :
    Slice.index_usize values i=ok (cell values i h) := by
  simp only [Slice.index_usize,Slice.getElem?_Usize_eq,List.getElem?_eq_getElem h,cell]

def appended (values : Slice W) (out : alloc.vec.Vec U8) (i : Usize)
    (h : i.val<values.val.length) (bound : out.length+32≤Usize.max) : alloc.vec.Vec U8 :=
  ProverRw21VecAppend.append out (Array.to_slice (ProverRw21FlatOutput.output (cell values i h)))
    (by simpa only [Slice.length,Array.to_slice,ProverRw21FlatOutput.output,
      ProverRw21FlatOutput.length] using bound)

theorem active (ops : ExternalFuns) (values : Slice W) (out : alloc.vec.Vec U8) (i : Usize)
    (h : i.val<values.val.length) (bound : out.length+32≤Usize.max) :
    @prover.encoded_slice_loop.body _ (selected ops) values out i =
      ok (cont (appended values out i h bound,Usize.wrapping_add i 1#usize)) := by
  have inside : i<Slice.len values := by exact h
  have serialize (x : W) :
      @aspis_core.field.wide_exact.WideExact.to_le_bytes _ (selected ops) x =
        ok (ProverRw21FlatOutput.output x) := ProverRw21FlatSourceLaw.exact x
  simp only [prover.encoded_slice_loop.body,inside,if_true,read values i h,
    serialize,bind_tc_ok,lift]
  rw [ProverRw21VecAppend.exact_append out _ (by
    simpa only [Slice.length,Array.to_slice,ProverRw21FlatOutput.output,
      ProverRw21FlatOutput.length] using bound)]
  rfl

theorem finished (ops : ExternalFuns) (values : Slice W) (out : alloc.vec.Vec U8) (i : Usize)
    (h : values.val.length ≤ i.val) :
    @prover.encoded_slice_loop.body _ (selected ops) values out i=ok (done out) := by
  have outside : ¬i<Slice.len values := by exact Nat.not_lt.mpr h
  simp only [prover.encoded_slice_loop.body,outside,if_false]

#print axioms read
#print axioms appended
#print axioms active
#print axioms finished
end R1Z.ProverRw21EncodedStep
