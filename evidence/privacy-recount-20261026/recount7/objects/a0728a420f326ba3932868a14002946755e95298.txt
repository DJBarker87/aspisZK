import Std
set_option autoImplicit false
namespace R1Z.PV_RW_Cursor

structure Cursor (T : Type) where
  values : List T
  index : Nat

def remaining {T : Type} (cursor : Cursor T) : List T := cursor.values.drop cursor.index

def next {T : Type} (cursor : Cursor T) : Option T × Cursor T :=
  if h : cursor.index < cursor.values.length then
    (some cursor.values[cursor.index],{cursor with index := cursor.index+1})
  else (none,cursor)

theorem initial {T : Type} (values : List T) : remaining (Cursor.mk values 0)=values := rfl

theorem some_step {T : Type} (cursor : Cursor T) (h : cursor.index<cursor.values.length) :
    next cursor=(some cursor.values[cursor.index],{cursor with index := cursor.index+1}) := by
  simp only [next,dif_pos h]

theorem none_step {T : Type} (cursor : Cursor T) (h : cursor.values.length≤cursor.index) :
    next cursor=(none,cursor) := by
  have no : ¬ cursor.index<cursor.values.length := by omega
  simp only [next,dif_neg no]

theorem backing {T : Type} (cursor : Cursor T) : (next cursor).2.values=cursor.values := by
  unfold next
  split <;> rfl

theorem contents_step {T : Type} (cursor : Cursor T) (h : cursor.index<cursor.values.length) :
    remaining cursor=cursor.values[cursor.index]::remaining (next cursor).2 := by
  rw [some_step cursor h]
  exact List.drop_eq_getElem_cons h

theorem remaining_length {T : Type} (cursor : Cursor T) :
    (remaining cursor).length=cursor.values.length-cursor.index := by
  simp only [remaining,List.length_drop]

theorem decreases {T : Type} (cursor : Cursor T) (h : cursor.index<cursor.values.length) :
    (remaining (next cursor).2).length+1=(remaining cursor).length := by
  rw [some_step cursor h]
  simp only [remaining_length]
  omega

theorem exhausted {T : Type} (cursor : Cursor T) (h : cursor.values.length≤cursor.index) :
    remaining cursor=[] := List.drop_eq_nil_of_le h

theorem bounded {T : Type} (cursor : Cursor T) (h : cursor.index≤cursor.values.length) :
    (next cursor).2.index≤(next cursor).2.values.length := by
  unfold next
  split
  · rename_i yes
    dsimp only
    omega
  · exact h
#print axioms initial
#print axioms some_step
#print axioms none_step
#print axioms backing
#print axioms contents_step
#print axioms remaining_length
#print axioms decreases
#print axioms exhausted
#print axioms bounded
end R1Z.PV_RW_Cursor
