import NJG_RowWindows
set_option autoImplicit false
namespace AspisR1.NJG_RowPrefixes
open NJG_RowWindows

/-- Complete selected-row prefix invariant for the three source writes,
uniform in every abort position. Arbitrary suffix prestate is preserved. -/
theorem selected_prefix {T : Type} (rows : Fin 3 → Nat → T) (before : Nat → T)
 (n : Nat) (bound : n≤3) (p : Fin 3) (i : Fin 116) :
 prefixState rows before n (116*p.val+i.val)=
 if p.val<n then rows p i.val else before (116*p.val+i.val) := by
 induction n with
 | zero=>simp only [prefixState,Nat.not_lt_zero,if_false]
 | succ n ih=>
   have hn:n<3:=by omega
   rw [prefixState,dif_pos hn]
   by_cases same:p.val=n
   · have eq:p=(⟨n,hn⟩ : Fin 3):=Fin.ext same
     subst p
     rw [selected,if_pos (by omega)]
   · have different:p≠(⟨n,hn⟩ : Fin 3):=fun h=>same (congrArg Fin.val h)
     rw [frame _ _ _ _ different,ih (by omega)]
     congr 1 <;> omega

theorem complete_rows {T : Type} (rows : Fin 3 → Nat → T) (before : Nat → T)
 (p : Fin 3) (i : Fin 116) :
 prefixState rows before 3 (116*p.val+i.val)=rows p i.val := by
 rw [selected_prefix rows before 3 (by omega),if_pos p.isLt]

/-- A row beyond an aborted prefix is never interpreted as an initialized
row. Its observed prestate is unchanged; no value is fabricated. -/
theorem abort_frame {T : Type} (rows : Fin 3 → Nat → T) (before : Nat → T)
 (n : Nat) (bound : n≤3) (p : Fin 3) (i : Fin 116) (later : n≤p.val) :
 prefixState rows before n (116*p.val+i.val)=before (116*p.val+i.val) := by
 rw [selected_prefix rows before n bound,if_neg (by omega)]

#print axioms selected_prefix
#print axioms complete_rows
#print axioms abort_frame
end AspisR1.NJG_RowPrefixes
