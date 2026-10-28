import NBL_InitTrace
set_option autoImplicit false
namespace AspisR1.NBL_InitConstruct
open Aeneas Aeneas.Std NBL_InitTrace

theorem frame {T : Type} (before : Words T) (i : Fin 8) (word : T) :
    ∃ after,Frame before after i word := by
  let after : Words T := ⟨List.ofFn (fun j : Fin 8 => if j=i then word else cell before j),by simp⟩
  refine ⟨after,?_⟩
  intro j
  simp only [cell,after,List.getElem_ofFn]

/-- Frame induction is inhabited for every arbitrary pre-state and every
bounded prefix, rather than presupposing a successful complete initialization. -/
theorem trace {T : Type} (word : Fin 8 → T) (n : Nat) (bound : n≤8) (before : Words T) :
    ∃ after,Trace word n before after := by
  induction n with
  | zero => exact ⟨before,.zero before⟩
  | succ n ih =>
    obtain ⟨middle,previous⟩ := ih (by omega)
    have small : n<8 := by omega
    obtain ⟨after,written⟩ := frame middle ⟨n,small⟩ (word ⟨n,small⟩)
    exact ⟨after,.step n before middle after small previous written⟩

theorem rho (block : Array U8 32#usize) (before : Words UInt32) :
    ∃ after,Trace (byteWord block) 8 before after ∧
      after.val.reverse=SamplerBytePass.digits block := by
  obtain ⟨after,initialized⟩ := trace (byteWord block) 8 (by omega) before
  exact ⟨after,initialized,NBL_InitTrace.rho initialized⟩

#print axioms frame
#print axioms trace
#print axioms rho
end AspisR1.NBL_InitConstruct
