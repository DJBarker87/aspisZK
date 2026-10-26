import R1Z.ProverRw18ComplexWrite
import R1Z.ProverRw18Overlay
set_option autoImplicit false
namespace R1Z.ProverRw18ComplexBytes
open Aeneas Aeneas.Std Result ProverRw18ComplexWrite

def bytes (x : C) : List U8 := (word x.a).val++(word x.b).val

theorem length (x : C) : (bytes x).length=8 := by
  simp only [bytes,List.length_append,word_length]

theorem output_value (x : C) (out : Slice U8) (bound : 8≤out.val.length) :
    (output x out).val=bytes x++out.val.drop 8 := by
  unfold output ProverRw18SliceWrite.put bytes
  change (out.val.setSlice! 0 (word x.a).val).setSlice! 4 (word x.b).val=_
  have h := ProverRw18Overlay.adjacent out.val (word x.a).val (word x.b).val
    (by simpa only [word_length] using bound)
  simpa only [word_length] using h

theorem exact_write (x : C) (out : Slice U8) (bound : 8≤out.val.length) :
    ∃ result : Slice U8, source x out=ok result ∧ result.val=bytes x++out.val.drop 8 :=
  ⟨output x out,ProverRw18ComplexWrite.exact_write x out bound,output_value x out bound⟩

#print axioms length
#print axioms output_value
#print axioms exact_write
end R1Z.ProverRw18ComplexBytes
