import NIX_FlatGeometry
import NIX_CertificateFrames
set_option autoImplicit false
namespace AspisR1.NJG_RowWindows
/-- A row occupies 116 u32 words. This is the KMX explicit-write value
semantics; it does not assert a native aggregate-write or allocator bridge. -/
def store {T : Type} (row before : Nat → T) (p : Fin 3) : Nat → T :=
 KMX_CopyMeaning.loop (fun k => row (k-116*p.val)) before (116*p.val) 116

theorem selected {T : Type} (row before : Nat → T) (p : Fin 3) (i : Fin 116) :
 store row before p (116*p.val+i.val)=row i.val := by
 rw [store,KMX_CopyMeaning.loop_spec,if_pos (by omega)]
 congr 1;omega

theorem frame {T : Type} (row before : Nat → T) (p q : Fin 3)
 (different : q≠p) (i : Fin 116) :
 store row before p (116*q.val+i.val)=before (116*q.val+i.val) := by
 apply KMX_CopyMeaning.copy_frame
 have d : q.val≠p.val := fun h=>different (Fin.ext h)
 omega

theorem word_index (p : Fin 3) (i : Fin 29) (limb : Fin 4) :
 NIX_FlatGeometry.word p i limb=116*p.val+(4*i.val+limb.val) ∧
 4*i.val+limb.val<116 := by
 unfold NIX_FlatGeometry.word;omega

/-- Extensional SAME-prestate law with the complete unchanged complement. -/
theorem complete {T : Type} (row before : Nat → T) (p : Fin 3) :
 store row before p=fun k=>if 116*p.val≤k ∧ k<116*(p.val+1)
 then row (k-116*p.val) else before k := by
 funext k
 rw [store,KMX_CopyMeaning.loop_spec]
 congr 1 <;> omega

/-- Every abort prefix retains the exact previous rows and arbitrary
uninitialised suffix representation. No suffix value is read natively. -/
def prefix {T : Type} (rows : Fin 3 → Nat → T) (before : Nat → T) : Nat → Nat → T
 | 0=>before
 | n+1=>if h:n<3 then store (rows ⟨n,h⟩) (prefix rows before n) ⟨n,h⟩
          else prefix rows before n

theorem prefix_frame {T : Type} (rows : Fin 3 → Nat → T) (before : Nat → T)
 (n k : Nat) (outside : 116*n≤k) : prefix rows before n k=before k := by
 induction n with
 | zero=>rfl
 | succ n ih=>
   rw [prefix]
   split
   · rw [store,KMX_CopyMeaning.copy_frame]
     · exact ih (by omega)
     · right;omega
   · exact ih (by omega)

#print axioms selected
#print axioms frame
#print axioms word_index
#print axioms complete
#print axioms prefix_frame
end AspisR1.NJG_RowWindows
