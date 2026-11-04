import NFM_Thread
import NFI_FailurePrefixes
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AspisR1.NFM_Cuts
open Aeneas Aeneas.Std Result NFI_TraceResult
abbrev Input := NFI_InnerCut.Input
abbrev Limbs := NFM_Thread.Limbs
structure Cut where
  position : Fin 7
  limbs : Limbs
  inner : NFI_InnerCut.Cut

def window (oracle : NFF_LoggedEight.Oracle) (input : Input) (k : Fin 7)
    (limbs : Limbs) : M Cut Limbs :=
  let before : NFI_InnerCut.Cut := ⟨input,
    {start:=NFA_Iterator.cursor ⟨k.val,by omega⟩,
     «end»:=NFA_Iterator.cursor ⟨k.val+1,by omega⟩},Array.repeat 8#usize 0#u64⟩
  let observed := NFI_InnerTrace.run oracle
    ((NFA_Iterator.cursor ⟨k.val+1,by omega⟩).val-
     (NFA_Iterator.cursor ⟨k.val,by omega⟩).val) before
  ⟨(do let out ← observed.1; NFE_NFA_FoldEight.eight out.sums limbs),
   observed.2.map (fun inner => ⟨k,limbs,inner⟩)⟩

theorem window_erased (oracle : NFF_LoggedEight.Oracle) (input : Input)
    (k : Fin 7) (limbs : Limbs) :
    (window oracle input k limbs).result=NFM_Thread.window oracle input k limbs := by
  simp only [window,NFI_InnerTrace.replay,NFM_Thread.window]
  cases h : NFF_LoggedLoop.run oracle input.q input.g input.slot
    ((NFA_Iterator.cursor ⟨k.val+1,by omega⟩).val-
     (NFA_Iterator.cursor ⟨k.val,by omega⟩).val)
    {start:=NFA_Iterator.cursor ⟨k.val,by omega⟩,
     «end»:=NFA_Iterator.cursor ⟨k.val+1,by omega⟩}
    (Array.repeat 8#usize 0#u64) <;> rfl

def sequence (oracle : NFF_LoggedEight.Oracle) (input : Input) :
    List (Fin 7) → Limbs → M Cut Limbs
  | [],limbs => pure limbs
  | k::rest,limbs => do
    let out ← window oracle input k limbs
    sequence oracle input rest out

theorem erased (oracle : NFF_LoggedEight.Oracle) (input : Input)
    (positions : List (Fin 7)) (limbs : Limbs) :
    (sequence oracle input positions limbs).result=NFM_Thread.thread oracle input positions limbs := by
  induction positions generalizing limbs with
  | nil => rfl
  | cons k rest ih =>
    simp only [sequence,erase_bind,window_erased,NFM_Thread.thread]
    congr 1
    funext out
    exact ih out

theorem main (oracle : NFF_LoggedEight.Oracle) (input : Input) (limbs : Limbs) :
    (sequence oracle input [0,1,2,3,4,5,6] limbs).result=
    NFF_LoggedOuterLoop.run oracle input.q input.g input.slot 7
      (NFA_Iterator.value 0) limbs := by
  rw [erased,NFM_Thread.main]

/-- A failed window retains its own prefix and executes no later window. -/
theorem abort_prefix (oracle : NFF_LoggedEight.Oracle) (input : Input)
    (k : Fin 7) (rest : List (Fin 7)) (limbs : Limbs) (e : Error)
    (failure : (window oracle input k limbs).result=fail e) :
    (sequence oracle input (k::rest) limbs).result=fail e ∧
    (sequence oracle input (k::rest) limbs).cuts=(window oracle input k limbs).cuts := by
  exact fail_prefix (window oracle input k limbs)
    (fun out => sequence oracle input rest out) e failure

#print axioms window_erased
#print axioms erased
#print axioms main
#print axioms abort_prefix
end AspisR1.NFM_Cuts
end
