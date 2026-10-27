import LPb_CheckpointLayout
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal
namespace LPb_ByteFold
/-- K004 compares the actual scalar writer against these four ordered words
on all raw u32 inputs. The checkpoint enclosing-loop native join is OPEN. -/
def words (x : aspis_core.field.QM31) : List U32 := [x.c0.a,x.c0.b,x.c1.a,x.c1.b]
def appendScalars (initialBytes : List U8) (xs : List aspis_core.field.QM31) : List U8 :=
  xs.foldl (fun out x => out ++ XRk_qBytes x) initialBytes

theorem scalar_words (x : aspis_core.field.QM31) : XRk_qBytes x = (words x).flatMap XRk_wordBytes := rfl

theorem append_spec (initialBytes : List U8) (xs : List aspis_core.field.QM31) :
    appendScalars initialBytes xs = initialBytes ++ xs.flatMap XRk_qBytes := by
  induction xs generalizing initialBytes with
  | nil => simp only [appendScalars,List.foldl_nil,List.flatMap_nil,List.append_nil]
  | cons x xs ih =>
    change appendScalars (initialBytes ++ XRk_qBytes x) xs = _
    rw [ih]
    simp only [List.flatMap_cons,List.append_assoc]

theorem weights_sequence (a : verifier.Accumulator) :
    a.weights.val.flatMap XRk_qBytes = appendScalars [] a.weights.val := by
  rw [append_spec,List.nil_append]

theorem word_length (x : U32) : (XRk_wordBytes x).length = 4 := by
  simp only [XRk_wordBytes,List.length_map,List.length_range]

theorem scalar_length (x : aspis_core.field.QM31) : (XRk_qBytes x).length = 16 := by
  simp only [XRk_qBytes,List.flatMap_cons,List.flatMap_nil,List.length_append,word_length,List.length_nil]

theorem scalars_length (xs : List aspis_core.field.QM31) :
    (xs.flatMap XRk_qBytes).length = 16 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,scalar_length,ih,List.length_cons]
    omega

theorem weights64 (a : verifier.Accumulator) (size : a.weights.val.length = 64) :
    (appendScalars [] a.weights.val).length = 1024 := by
  rw [append_spec,List.nil_append,scalars_length,size]
#print axioms scalar_words
#print axioms append_spec
#print axioms weights_sequence
#print axioms word_length
#print axioms scalar_length
#print axioms scalars_length
#print axioms weights64
end LPb_ByteFold
