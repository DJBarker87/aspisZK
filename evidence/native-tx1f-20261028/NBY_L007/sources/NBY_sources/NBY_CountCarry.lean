import NBY_CountExecution

set_option autoImplicit false
namespace AspisR1.NBY_CountCarry

/-- The Rust accumulator is carried across levels. Its row writes and scan
cursor do not depend on the prior count. -/
theorem rows_shift (fuel : Nat) (key : Nat → Nat) (n i w count shift : Nat) :
    NBJ_CountRows.nativeRows fuel key n i w (count+shift) =
      let out := NBJ_CountRows.nativeRows fuel key n i w count
      (out.1,out.2+shift) := by
  induction fuel generalizing key i w count with
  | zero => rfl
  | succ fuel ih =>
    by_cases active : i < n
    · simp only [NBJ_CountRows.nativeRows,if_pos active]
      let j := NBI_CountScan.scan key (key i/2) n (n-i) i
      have reorder : count+shift+(2-(j-i)) = (count+(2-(j-i)))+shift := by omega
      rw [reorder,ih]
    · simp only [NBJ_CountRows.nativeRows,if_neg active]

def carry : Nat → (Nat → Nat) → Nat → Nat → Nat
  | 0,_,_,count => count
  | height+1,key,n,count =>
      let out := NBJ_CountRows.nativeRows n key n 0 0 count
      carry height (fun j => out.1[j]!) out.1.length out.2

/-- Constructed single global accumulation agrees with the inherited local
level sum. Each next key carrier is the SAME preceding row execution's result. -/
theorem carry_eq (height : Nat) (key : Nat → Nat) (n count : Nat) :
    carry height key n count = count+NBJ_CountLevels.nativeCount height key n := by
  induction height generalizing key n count with
  | zero => simp only [carry,NBJ_CountLevels.nativeCount,Nat.add_zero]
  | succ height ih =>
    have shifted := rows_shift n key n 0 0 0 count
    simp only [Nat.zero_add] at shifted
    rw [carry,shifted]
    simp only
    rw [ih,NBJ_CountLevels.nativeCount]
    omega

/-- The exact single-accumulator model consumes the existing copied prestate
and eighteen-level source projection, without a final-count premise. -/
theorem initialized (key : Nat → Nat) (n count : Nat)
    (ordered : (MultiproofConeCountPhysical.cells key 0 n).Pairwise (·<·)) :
    carry 18 (NBV_CountInitialization.initialized key n) n count =
      count+MultiproofConeCountLevels.sourceCount 18
        (MultiproofConeCountPhysical.cells key 0 n) := by
  rw [carry_eq,NBV_CountInitialization.count_initialized key n ordered]

#print axioms rows_shift
#print axioms carry_eq
#print axioms initialized
end AspisR1.NBY_CountCarry
