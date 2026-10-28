import R1Z.PV_RDB1_PointerConstruct
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_V198

/-- Byte-buffer effects stay visible on failure; Result alone is insufficient
for a writer that may panic after writing its first subrange. -/
structure Execution where
  returned : Result Unit
  bytes : List U8

def words (a b : U32) : List U8 :=
  (core.num.U32.to_le_bytes a).val ++ (core.num.U32.to_le_bytes b).val

theorem words_length (a b : U32) : (words a b).length = 8 := by
  have ha := (core.num.U32.to_le_bytes a).property
  have hb := (core.num.U32.to_le_bytes b).property
  change (core.num.U32.to_le_bytes a).val.length=4 at ha
  change (core.num.U32.to_le_bytes b).val.length=4 at hb
  simp only [words,List.length_append,ha,hb]

def write (a b c d : U32) (out : List U8) : Execution :=
  if out.length < 8 then ⟨fail .panic,out⟩ else
  let afterFirst := words a b ++ out.drop 8
  if out.length < 16 then ⟨fail .panic,afterFirst⟩ else
  ⟨ok (),words a b ++ words c d ++ out.drop 16⟩

/-- The deployed outer slicing order is 0..8, write c0, then 8..16,
write c1. A short second range retains c0's writes in the caller's buffer. -/
def reference (a b c d : U32) (out : List U8) : Execution :=
  if out.length < 8 then ⟨fail .panic,out⟩ else
  if out.length < 16 then ⟨fail .panic,words a b ++ out.drop 8⟩ else
  ⟨ok (),words a b ++ words c d ++ out.drop 16⟩

theorem complete (a b c d : U32) (out : List U8) :
    write a b c d out = reference a b c d out := rfl

theorem short_first (a b c d : U32) (out : List U8) (h : out.length < 8) :
    write a b c d out = ⟨fail .panic,out⟩ := by simp only [write,h,ite_true]

theorem short_second (a b c d : U32) (out : List U8)
    (h8 : 8 ≤ out.length) (h16 : out.length < 16) :
    write a b c d out = ⟨fail .panic,words a b ++ out.drop 8⟩ := by
  simp only [write,Nat.not_lt.mpr h8,h16,ite_false,ite_true]

theorem full (a b c d : U32) (out : List U8) (h : 16 ≤ out.length) :
    write a b c d out = ⟨ok (),words a b ++ words c d ++ out.drop 16⟩ := by
  have h8 : ¬ out.length < 8 := by omega
  simp only [write,h8,Nat.not_lt.mpr h,ite_false]

/-- Mutable range writes preserve total length in every branch; the scalar
array sources are always exactly four bytes, so copy length errors cannot
occur after a successful outer range check. -/
theorem length_preserved (a b c d : U32) (out : List U8) :
    (write a b c d out).bytes.length = out.length := by
  by_cases h8 : out.length < 8
  · rw [short_first a b c d out h8]
  · by_cases h16 : out.length < 16
    · rw [short_second a b c d out (by omega) h16]
      simp only [List.length_append,List.length_drop,words_length]
      omega
    · rw [full a b c d out (by omega)]
      simp only [List.length_append,List.length_drop,words_length]
      omega

/-- Complete error status, including the length range whose buffer is
partially written. The caller can inspect the effect via Execution.bytes. -/
theorem status (a b c d : U32) (out : List U8) :
    (write a b c d out).returned =
      if out.length < 16 then fail .panic else ok () := by
  unfold write
  by_cases h8 : out.length < 8
  · have h16 : out.length < 16 := by omega
    simp only [h8,h16,ite_true]
  · simp only [h8,ite_false]
    split <;> rfl

#print axioms words_length
#print axioms complete
#print axioms short_first
#print axioms short_second
#print axioms full
#print axioms length_preserved
#print axioms status
end R1Z.PV_RDB1_V198
