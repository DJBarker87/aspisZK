import NHB_FullFrame
set_option autoImplicit false
namespace AspisR1.NHB_Reference
open Aeneas Aeneas.Std
abbrev State := NGQ_SamplerTrace.State

/-- Positional correspondence with the six scalar fields of NHB_word_ref.
The arbitrary window is typed with the SAME22-cell survivor array. -/
structure Fields where
  stop : Bool
  candidate : U32
  cursor : Nat
  length : Nat
  draws : Nat
  word : U32

def fields (s : State) (x : U32) (cursor : Nat) (j : Fin 22) : Fields :=
  let halted := decide (s.accepted_len.val=22 ∨ s.draws.val=64)
  let member := NHB_Membership.reference x (s.accepted.val.take s.accepted_len.val)
  {stop:=halted,candidate:=x,cursor:=cursor+1,
   length:=if halted || member then s.accepted_len.val else s.accepted_len.val+1,
   draws:=if halted then s.draws.val else s.draws.val+1,
   word:=if !halted && !member && decide (j.val=s.accepted_len.val) then x
     else s.accepted.val[j.val]'(by have := s.accepted.property; change s.accepted.val.length=22 at this; omega)}

theorem stopped (s : State) (x : U32) (cursor : Nat) (j : Fin 22)
    (full : s.accepted_len.val=22 ∨ s.draws.val=64) :
    (fields s x cursor j).stop=true ∧
    (fields s x cursor j).cursor=cursor+1 ∧
    (fields s x cursor j).length=s.accepted_len.val ∧
    (fields s x cursor j).draws=s.draws.val ∧
    (fields s x cursor j).word=
      s.accepted.val[j.val]'(by have := s.accepted.property; change s.accepted.val.length=22 at this; omega) := by
  have halt : decide (s.accepted_len.val=22 ∨ s.draws.val=64)=true := by simp only [full,decide_true]
  simp [fields,halt]

theorem continuing (s : State) (x : U32) (cursor : Nat) (j : Fin 22)
    (hlen : s.accepted_len.val<22) (hdraw : s.draws.val<64) :
    (fields s x cursor j).stop=false ∧
    (fields s x cursor j).cursor=cursor+1 ∧
    (fields s x cursor j).draws=s.draws.val+1 ∧
    (fields s x cursor j).length=s.accepted_len.val+
      (if NHB_Membership.reference x (s.accepted.val.take s.accepted_len.val) then 0 else 1) := by
  have notfull : ¬(s.accepted_len.val=22 ∨ s.draws.val=64) := by omega
  have halt : decide (s.accepted_len.val=22 ∨ s.draws.val=64)=false := by simp only [notfull,decide_false]
  cases member : NHB_Membership.reference x (s.accepted.val.take s.accepted_len.val) <;>
    simp [fields,halt,member]

theorem set_window (s : State) (x : U32) (j : Fin 22) :
    (s.accepted.set s.accepted_len x).val[j.val]'(by
      have := (s.accepted.set s.accepted_len x).property
      change (s.accepted.set s.accepted_len x).val.length=22 at this
      omega)=
    (if j.val=s.accepted_len.val then x else
      s.accepted.val[j.val]'(by have := s.accepted.property; change s.accepted.val.length=22 at this; omega)) := by
  change (s.accepted.val.set s.accepted_len.val x)[j.val] = _
  simp only [List.getElem_set,eq_comm]

#print axioms stopped
#print axioms continuing
#print axioms set_window
end AspisR1.NHB_Reference
