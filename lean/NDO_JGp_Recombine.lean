import NDO_JGn_PrepareBuffer
set_option autoImplicit false
namespace AspisR1.JGp_Recombine
open Aeneas Aeneas.Std Result

def vector (semantic y1 : Slice U8) : alloc.vec.Vec U8 :=
  ⟨(JGn_PrepareBuffer.back (semantic,y1)).val,(JGn_PrepareBuffer.back (semantic,y1)).property⟩

theorem take (semantic y1 : Slice U8) (hs : semantic.length=13831) (hy : y1.length=928) :
    (vector semantic y1).val.take 13831=semantic.val := by
  change (JGn_PrepareBuffer.back (semantic,y1)).val.take 13831=semantic.val
  rw [JGn_PrepareBuffer.recombine semantic y1 hs hy]
  have size : semantic.val.length=13831 := hs
  rw [←size,List.take_left]
#print axioms take

theorem drop (semantic y1 : Slice U8) (hs : semantic.length=13831) (hy : y1.length=928) :
    (vector semantic y1).val.drop 13831=y1.val := by
  change (JGn_PrepareBuffer.back (semantic,y1)).val.drop 13831=y1.val
  rw [JGn_PrepareBuffer.recombine semantic y1 hs hy]
  have size : semantic.val.length=13831 := hs
  rw [←size,List.drop_left]
#print axioms drop

theorem length (semantic y1 : Slice U8) (hs : semantic.length=13831) (hy : y1.length=928) :
    (vector semantic y1).val.length=14759 := by
  change (JGn_PrepareBuffer.back (semantic,y1)).val.length=14759
  rw [JGn_PrepareBuffer.recombine semantic y1 hs hy,List.length_append]
  change semantic.length+y1.length=14759
  rw [hs,hy]
#print axioms length
end AspisR1.JGp_Recombine
