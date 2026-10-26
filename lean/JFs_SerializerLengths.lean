import PublicSerializerWhole431
set_option autoImplicit false
namespace AspisR1.JFs_SerializerLengths
open Aeneas Aeneas.Std Result
open AspisR1PublicSerializer.FieldsRefinement431
open AspisR1PublicSerializer.Frontier431
open AspisR1PublicSerializer.Whole431

theorem words (xs : List Field) : (encodeWords xs).length=4*xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [encodeWords,List.flatMap_cons,List.length_append,wordBytes_length,
      List.length_cons] at *
    omega

theorem row_length (values : Frontier) (i : Fin 20) : (row values i).val.length=8 := by
  exact (values.val[i.val]'(by rw [values.property];exact i.isLt)).property

theorem frontier_words (values : Frontier) : ((rows values).flatMap (fun s => s.val)).length=160 := by
  simp only [rows,List.flatMap_cons,List.flatMap_nil,List.length_append,row_length,List.length_nil]

theorem frontier_bytes (values : Frontier) :
    (encodeWords ((rows values).flatMap (fun s => s.val))).length=640 := by
  rw [words,frontier_words]

#print axioms words
#print axioms row_length
#print axioms frontier_words
#print axioms frontier_bytes
end AspisR1.JFs_SerializerLengths
