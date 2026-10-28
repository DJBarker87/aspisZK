import NBA_Rho
set_option autoImplicit false
namespace AspisR1.NBL_InitTrace
open Aeneas Aeneas.Std
abbrev Words (T : Type) := Array T 8#usize

def cell {T : Type} (a : Words T) (i : Fin 8) : T :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)

def Frame {T : Type} (before after : Words T) (i : Fin 8) (word : T) : Prop :=
  ∀ j : Fin 8,cell after j=if j=i then word else cell before j

inductive Trace {T : Type} (word : Fin 8 → T) : Nat → Words T → Words T → Prop where
  | zero (a : Words T) : Trace word 0 a a
  | step (n : Nat) (before middle after : Words T) (bound : n<8)
      (history : Trace word n before middle)
      (write : Frame middle after ⟨n,bound⟩ (word ⟨n,bound⟩)) :
      Trace word (n+1) before after

theorem processed {T : Type} {word : Fin 8 → T} {n : Nat} {before after : Words T}
    (tr : Trace word n before after) : ∀ j : Fin 8,j.val<n → cell after j=word j := by
  induction tr with
  | zero a => intro j h;omega
  | step n before middle after bound previous write ih =>
    intro j hj
    rw [write j]
    by_cases eqn : j=⟨n,bound⟩
    · simp only [eqn,↓reduceIte]
    · simp only [eqn,↓reduceIte]
      have ne : j.val≠n := by intro h;exact eqn (Fin.ext h)
      exact ih j (by omega)

theorem source {T : Type} {word : Fin 8 → T} {before after : Words T}
    (tr : Trace word 8 before after) : after.val=List.ofFn word := by
  apply List.ext_getElem
  · simp only [List.length_ofFn]
    exact after.property
  · intro i hi hj
    have bound : i<8 := by have := after.property;change after.val.length=8 at this;omega
    simpa only [cell,List.getElem_ofFn] using processed tr ⟨i,bound⟩ bound

def byteWord (block : Array U8 32#usize) (i : Fin 8) : UInt32 :=
  (SamplerBytePass.digits block).reverse[i.val]'(by
    rw [List.length_reverse,SamplerBytePass.digits_length];exact i.isLt)

/-- K011 byte initialization frames compose to the EXACT ordered input of the
four-pass rho division trace; arbitrary previous rank contents disappear. -/
theorem rho {block : Array U8 32#usize} {before after : Words UInt32}
    (tr : Trace (byteWord block) 8 before after) : after.val.reverse=SamplerBytePass.digits block := by
  rw [source tr]
  have words : List.ofFn (byteWord block)=(SamplerBytePass.digits block).reverse := by
    apply List.ext_getElem
    · simp only [List.length_ofFn,List.length_reverse,SamplerBytePass.digits_length]
    · intro i hi hj
      simp only [List.getElem_ofFn,byteWord]
  rw [words,List.reverse_reverse]

#print axioms processed
#print axioms source
#print axioms rho
end AspisR1.NBL_InitTrace
