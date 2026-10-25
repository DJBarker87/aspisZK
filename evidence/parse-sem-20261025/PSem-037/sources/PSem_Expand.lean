import MultiproofConeExpandModel
set_option autoImplicit false
namespace AspisR1.PSem_Expand
open AspisV8R19.DuplexFrames OraclePortCompactDraft
open MultiproofConeExpandModel

theorem expand_length (n : Nat) (b : Bytes) (length : b.length = 16*n) :
    (expand n b).length = 32*n := by
  induction n generalizing b with
  | zero => simp [expand]
  | succ n ih =>
    rw [expand_step]
    have enough : 16 ≤ b.length := by omega
    have rest : (b.drop 16).length=16*n := by rw [List.length_drop];omega
    rw [List.length_append,List.length_append,List.length_take,List.length_replicate,
      Nat.min_eq_left enough,ih _ rest]
    omega

theorem expand_byte (n : Nat) (b : Bytes) (length : b.length=16*n)
    (j : Nat) (bound : j<32*n) :
    (expand n b)[j]? =
      if j%32<16 then b[(j/32)*16+j%32]? else some 0 := by
  induction n generalizing b j with
  | zero => omega
  | succ n ih =>
    rw [expand_step]
    have enough : 16 ≤ b.length := by omega
    have firstLength : (b.take 16).length=16 := by
      simp only [List.length_take,Nat.min_eq_left enough]
    have zeroLength : (List.replicate 16 (0 : Fin 256)).length=16 := by rfl
    by_cases low : j<16
    · have jm : j%32=j := Nat.mod_eq_of_lt (by omega)
      have jd : j/32=0 := Nat.div_eq_of_lt (by omega)
      rw [List.getElem?_append_left (by rw [List.length_append,firstLength,zeroLength];omega),
        List.getElem?_append_left (by rw [firstLength];exact low)]
      simp [List.getElem?_take,low,jm,jd]
    · by_cases middle : j<32
      · rw [List.getElem?_append_left (by rw [List.length_append,firstLength,zeroLength];omega),
          List.getElem?_append_right (by rw [firstLength];omega),firstLength]
        have jm : j%32=j := Nat.mod_eq_of_lt middle
        simp [List.getElem?_replicate,jm,low,show j-16<16 by omega]
      · rw [List.getElem?_append_right (by rw [List.length_append,firstLength,zeroLength];omega)]
        simp only [List.length_append,firstLength,zeroLength]
        have rest : (b.drop 16).length=16*n := by rw [List.length_drop];omega
        rw [ih _ rest (j-32) (by omega)]
        have jm : (j-32)%32=j%32 := by omega
        have jd : (j-32)/32=j/32-1 := by omega
        rw [jm,jd]
        split
        · rw [List.getElem?_drop]
          congr 1
          omega
        · rfl

#print axioms expand_length
#print axioms expand_byte
end AspisR1.PSem_Expand
