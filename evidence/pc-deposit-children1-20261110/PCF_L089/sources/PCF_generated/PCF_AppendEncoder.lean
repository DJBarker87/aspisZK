import PCF_DigestFirst
import PCB_AppendFullRef.Funs
import PCF_ArrayIndex
import PCF_EncodeByte
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCF_AppendEncoder
/-- Fixed eight symbolic words, four bytes each: no recurrence or concrete field reduction. -/
theorem words (a b c d e f g h : U32) :
    PCB_AppendFullRef.encode_digest_canonical (PCF_DigestFirst.words a b c d e f g h) =
      ok (AspisR1.S2K.DigestBytes.bytes (PCF_DigestFirst.words a b c d e f g h)) := by
  simp [PCB_AppendFullRef.encode_digest_canonical, PCF_ArrayIndex.result,
    Array.length_eq, PCF_DigestFirst.words, Array.make, lift, bind_tc_ok]
  apply Subtype.ext
  apply List.ext_getElem
  · exact (AspisR1.S2K.DigestBytes.bytes _).property.symm
  · intro i hi hj
    have hi32 : i < 32 := by simpa using hi
    have hw : i / 4 < ([a,b,c,d,e,f,g,h] : List U32).length := by simp only [List.length_cons,List.length_nil]; omega
    have hb := PCF_EncodeByte.at_word [a,b,c,d,e,f,g,h] 0
      (Array.repeat 32#usize 0#u8) (i/4) (i%4) hw (by omega) (by omega)
    have hidx : 4*(0+i/4)+i%4 = i := by omega
    rw [hidx] at hb
    change (AspisR1.S2K.DigestBytes.bytes (PCF_DigestFirst.words a b c d e f g h)).val[i]! = _ at hb
    have hl := List.getElem?_eq_getElem hi
    have hr := List.getElem?_eq_getElem hj
    have hgetl := List.getElem!_of_getElem? hl
    have hgetr := List.getElem!_of_getElem? hr
    rw [← hgetl,← hgetr,hb]
    generalize hk : (⟨i,hi32⟩ : Fin 32) = k
    have hv : i = k.val := congrArg Fin.val hk
    simp only [hv]
    fin_cases k <;> simp [Array.repeat, PCF_DigestFirst.words, Array.make]

#print axioms words
end PCF_AppendEncoder
