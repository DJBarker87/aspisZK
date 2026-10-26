import R1Z.ProverRw18QuarticWrite
set_option autoImplicit false
namespace R1Z.ProverRw18QuarticBytes
open Aeneas Aeneas.Std Result ProverRw18QuarticWrite

def bytes (x : Q) : List U8 :=
  ProverRw18ComplexBytes.bytes x.c0++ProverRw18ComplexBytes.bytes x.c1

theorem length (x : Q) : (bytes x).length=16 := by
  simp only [bytes,List.length_append,ProverRw18ComplexBytes.length]

theorem output_value (x : Q) (out : Slice U8) (bound : 16≤out.val.length) :
    (output x out).val=bytes x++out.val.drop 16 := by
  unfold output ProverRw18ComplexRegion.output bytes
  change (out.val.setSlice! 0 (ProverRw18ComplexBytes.bytes x.c0)).setSlice! 8
    (ProverRw18ComplexBytes.bytes x.c1)=_
  have h := ProverRw18Overlay.adjacent out.val (ProverRw18ComplexBytes.bytes x.c0)
    (ProverRw18ComplexBytes.bytes x.c1)
    (by simpa only [ProverRw18ComplexBytes.length] using bound)
  simpa only [ProverRw18ComplexBytes.length] using h

theorem exact_write (x : Q) (out : Slice U8) (bound : 16≤out.val.length) :
    ∃ result : Slice U8,source x out=ok result ∧ result.val=bytes x++out.val.drop 16 :=
  ⟨output x out,ProverRw18QuarticWrite.exact_write x out bound,output_value x out bound⟩

#print axioms length
#print axioms output_value
#print axioms exact_write
end R1Z.ProverRw18QuarticBytes
