import PV_EVH_StackStores
import PV_EVH_EntropyCallerLayout
set_option autoImplicit false
namespace PV_EVH_EntropyReturnFootprint
open PV_EVH_StackZero (State)
open PV_EVH_StackStores (Store Outside run)
open PV_EVH_EntropyCallerLayout (mask result caller)

/-- Captured source/register values at the accepted branch of the adopted
artifact. These are physical memory laws, not an installed native family.
Source/ABI interpretation and all register/spill/L3 observations remain P.
No moved-from inner slot or staging byte is cleared by these stores. -/
def stageFieldHigh (sp : Nat) (w : State) : Store := ⟨sp+176,16,fun i => w.memory (sp+16+i)⟩
def stageFieldLow (sp : Nat) (w : State) : Store := ⟨sp+160,16,fun i => w.memory (sp+i)⟩
def stageSeedLow (sp : Nat) (w : State) : Store := ⟨sp+192,16,fun i => w.memory (sp+32+i)⟩
def stageSeedHigh (sp : Nat) (w : State) : Store := ⟨sp+208,16,fun i => w.memory (sp+48+i)⟩
def stageMaskHigh (sp : Nat) (w : State) : Store := ⟨sp+144,16,fun i => w.memory (mask sp+16+i)⟩
def stageMaskLow (sp : Nat) (w : State) : Store := ⟨sp+128,16,fun i => w.memory (mask sp+i)⟩
def returnSeedHigh (sp : Nat) (w : State) : Store := ⟨result sp+81,16,fun i => w.memory (sp+48+i)⟩
def returnMaskHigh (sp : Nat) (w : State) : Store := ⟨result sp+17,16,fun i => w.memory (mask sp+16+i)⟩
def returnMaskLow (sp : Nat) (w : State) : Store := ⟨result sp+1,16,fun i => w.memory (mask sp+i)⟩
def returnSeedLow (sp : Nat) (w : State) : Store := ⟨result sp+65,16,fun i => w.memory (sp+32+i)⟩
def returnFieldHigh (sp : Nat) (w : State) : Store := ⟨result sp+49,16,fun i => w.memory (sp+16+i)⟩
def returnFieldLow (sp : Nat) (w : State) : Store := ⟨result sp+33,16,fun i => w.memory (sp+i)⟩
def tag (sp : Nat) (w : State) : Store := ⟨result sp,1,fun _ => 0⟩

def stores (sp : Nat) (w : State) : List Store :=
  [stageFieldHigh sp w,stageFieldLow sp w,stageSeedLow sp w,stageSeedHigh sp w,stageMaskHigh sp w,stageMaskLow sp w,returnSeedHigh sp w,returnMaskHigh sp w,returnMaskLow sp w,returnSeedLow sp w,returnFieldHigh sp w,returnFieldLow sp w,tag sp w]

def moved (sp : Nat) (w : State) : State := run (stores sp w) w

theorem stageFieldHigh_byte (sp : Nat) (w : State) (i : Nat) (hi : i < 16) :
    (moved sp w).memory (sp+176+i) = w.memory (sp+16+i) := by
  apply PV_EVH_StackStores.selected [] [stageFieldLow sp w,stageSeedLow sp w,stageSeedHigh sp w,stageMaskHigh sp w,stageMaskLow sp w,returnSeedHigh sp w,returnMaskHigh sp w,returnMaskLow sp w,returnSeedLow sp w,returnFieldHigh sp w,returnFieldLow sp w,tag sp w] (stageFieldHigh sp w) w i hi
  intro t ht
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Outside,stageFieldLow,stageSeedLow,stageSeedHigh,stageMaskHigh,stageMaskLow,returnSeedHigh,returnMaskHigh,returnMaskLow,returnSeedLow,returnFieldHigh,returnFieldLow,tag,result,mask,caller]
    omega

theorem stageFieldLow_byte (sp : Nat) (w : State) (i : Nat) (hi : i < 16) :
    (moved sp w).memory (sp+160+i) = w.memory (sp+i) := by
  apply PV_EVH_StackStores.selected [stageFieldHigh sp w] [stageSeedLow sp w,stageSeedHigh sp w,stageMaskHigh sp w,stageMaskLow sp w,returnSeedHigh sp w,returnMaskHigh sp w,returnMaskLow sp w,returnSeedLow sp w,returnFieldHigh sp w,returnFieldLow sp w,tag sp w] (stageFieldLow sp w) w i hi
  intro t ht
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Outside,stageSeedLow,stageSeedHigh,stageMaskHigh,stageMaskLow,returnSeedHigh,returnMaskHigh,returnMaskLow,returnSeedLow,returnFieldHigh,returnFieldLow,tag,result,mask,caller]
    omega

theorem stageSeedLow_byte (sp : Nat) (w : State) (i : Nat) (hi : i < 16) :
    (moved sp w).memory (sp+192+i) = w.memory (sp+32+i) := by
  apply PV_EVH_StackStores.selected [stageFieldHigh sp w,stageFieldLow sp w] [stageSeedHigh sp w,stageMaskHigh sp w,stageMaskLow sp w,returnSeedHigh sp w,returnMaskHigh sp w,returnMaskLow sp w,returnSeedLow sp w,returnFieldHigh sp w,returnFieldLow sp w,tag sp w] (stageSeedLow sp w) w i hi
  intro t ht
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Outside,stageSeedHigh,stageMaskHigh,stageMaskLow,returnSeedHigh,returnMaskHigh,returnMaskLow,returnSeedLow,returnFieldHigh,returnFieldLow,tag,result,mask,caller]
    omega

theorem stageSeedHigh_byte (sp : Nat) (w : State) (i : Nat) (hi : i < 16) :
    (moved sp w).memory (sp+208+i) = w.memory (sp+48+i) := by
  apply PV_EVH_StackStores.selected [stageFieldHigh sp w,stageFieldLow sp w,stageSeedLow sp w] [stageMaskHigh sp w,stageMaskLow sp w,returnSeedHigh sp w,returnMaskHigh sp w,returnMaskLow sp w,returnSeedLow sp w,returnFieldHigh sp w,returnFieldLow sp w,tag sp w] (stageSeedHigh sp w) w i hi
  intro t ht
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Outside,stageMaskHigh,stageMaskLow,returnSeedHigh,returnMaskHigh,returnMaskLow,returnSeedLow,returnFieldHigh,returnFieldLow,tag,result,mask,caller]
    omega

theorem stageMaskHigh_byte (sp : Nat) (w : State) (i : Nat) (hi : i < 16) :
    (moved sp w).memory (sp+144+i) = w.memory (mask sp+16+i) := by
  apply PV_EVH_StackStores.selected [stageFieldHigh sp w,stageFieldLow sp w,stageSeedLow sp w,stageSeedHigh sp w] [stageMaskLow sp w,returnSeedHigh sp w,returnMaskHigh sp w,returnMaskLow sp w,returnSeedLow sp w,returnFieldHigh sp w,returnFieldLow sp w,tag sp w] (stageMaskHigh sp w) w i hi
  intro t ht
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Outside,stageMaskLow,returnSeedHigh,returnMaskHigh,returnMaskLow,returnSeedLow,returnFieldHigh,returnFieldLow,tag,result,mask,caller]
    omega

theorem stageMaskLow_byte (sp : Nat) (w : State) (i : Nat) (hi : i < 16) :
    (moved sp w).memory (sp+128+i) = w.memory (mask sp+i) := by
  apply PV_EVH_StackStores.selected [stageFieldHigh sp w,stageFieldLow sp w,stageSeedLow sp w,stageSeedHigh sp w,stageMaskHigh sp w] [returnSeedHigh sp w,returnMaskHigh sp w,returnMaskLow sp w,returnSeedLow sp w,returnFieldHigh sp w,returnFieldLow sp w,tag sp w] (stageMaskLow sp w) w i hi
  intro t ht
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Outside,returnSeedHigh,returnMaskHigh,returnMaskLow,returnSeedLow,returnFieldHigh,returnFieldLow,tag,result,mask,caller]
    omega

theorem returnSeedHigh_byte (sp : Nat) (w : State) (i : Nat) (hi : i < 16) :
    (moved sp w).memory (result sp+81+i) = w.memory (sp+48+i) := by
  apply PV_EVH_StackStores.selected [stageFieldHigh sp w,stageFieldLow sp w,stageSeedLow sp w,stageSeedHigh sp w,stageMaskHigh sp w,stageMaskLow sp w] [returnMaskHigh sp w,returnMaskLow sp w,returnSeedLow sp w,returnFieldHigh sp w,returnFieldLow sp w,tag sp w] (returnSeedHigh sp w) w i hi
  intro t ht
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Outside,returnMaskHigh,returnMaskLow,returnSeedLow,returnFieldHigh,returnFieldLow,tag,result,mask,caller]
    omega

theorem returnMaskHigh_byte (sp : Nat) (w : State) (i : Nat) (hi : i < 16) :
    (moved sp w).memory (result sp+17+i) = w.memory (mask sp+16+i) := by
  apply PV_EVH_StackStores.selected [stageFieldHigh sp w,stageFieldLow sp w,stageSeedLow sp w,stageSeedHigh sp w,stageMaskHigh sp w,stageMaskLow sp w,returnSeedHigh sp w] [returnMaskLow sp w,returnSeedLow sp w,returnFieldHigh sp w,returnFieldLow sp w,tag sp w] (returnMaskHigh sp w) w i hi
  intro t ht
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Outside,returnMaskLow,returnSeedLow,returnFieldHigh,returnFieldLow,tag,result,mask,caller]
    omega

theorem returnMaskLow_byte (sp : Nat) (w : State) (i : Nat) (hi : i < 16) :
    (moved sp w).memory (result sp+1+i) = w.memory (mask sp+i) := by
  apply PV_EVH_StackStores.selected [stageFieldHigh sp w,stageFieldLow sp w,stageSeedLow sp w,stageSeedHigh sp w,stageMaskHigh sp w,stageMaskLow sp w,returnSeedHigh sp w,returnMaskHigh sp w] [returnSeedLow sp w,returnFieldHigh sp w,returnFieldLow sp w,tag sp w] (returnMaskLow sp w) w i hi
  intro t ht
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  all_goals
    simp only [Outside,returnSeedLow,returnFieldHigh,returnFieldLow,tag,result,mask,caller]
    omega

theorem returnSeedLow_byte (sp : Nat) (w : State) (i : Nat) (hi : i < 16) :
    (moved sp w).memory (result sp+65+i) = w.memory (sp+32+i) := by
  apply PV_EVH_StackStores.selected [stageFieldHigh sp w,stageFieldLow sp w,stageSeedLow sp w,stageSeedHigh sp w,stageMaskHigh sp w,stageMaskLow sp w,returnSeedHigh sp w,returnMaskHigh sp w,returnMaskLow sp w] [returnFieldHigh sp w,returnFieldLow sp w,tag sp w] (returnSeedLow sp w) w i hi
  intro t ht
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl
  all_goals
    simp only [Outside,returnFieldHigh,returnFieldLow,tag,result,mask,caller]
    omega

theorem returnFieldHigh_byte (sp : Nat) (w : State) (i : Nat) (hi : i < 16) :
    (moved sp w).memory (result sp+49+i) = w.memory (sp+16+i) := by
  apply PV_EVH_StackStores.selected [stageFieldHigh sp w,stageFieldLow sp w,stageSeedLow sp w,stageSeedHigh sp w,stageMaskHigh sp w,stageMaskLow sp w,returnSeedHigh sp w,returnMaskHigh sp w,returnMaskLow sp w,returnSeedLow sp w] [returnFieldLow sp w,tag sp w] (returnFieldHigh sp w) w i hi
  intro t ht
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl
  all_goals
    simp only [Outside,returnFieldLow,tag,result,mask,caller]
    omega

theorem returnFieldLow_byte (sp : Nat) (w : State) (i : Nat) (hi : i < 16) :
    (moved sp w).memory (result sp+33+i) = w.memory (sp+i) := by
  apply PV_EVH_StackStores.selected [stageFieldHigh sp w,stageFieldLow sp w,stageSeedLow sp w,stageSeedHigh sp w,stageMaskHigh sp w,stageMaskLow sp w,returnSeedHigh sp w,returnMaskHigh sp w,returnMaskLow sp w,returnSeedLow sp w,returnFieldHigh sp w] [tag sp w] (returnFieldLow sp w) w i hi
  intro t ht
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
  subst t
  all_goals
    simp only [Outside,tag,result,mask,caller]
    omega

theorem tag_byte (sp : Nat) (w : State) (i : Nat) (hi : i < 1) :
    (moved sp w).memory (result sp+i) = 0 := by
  apply PV_EVH_StackStores.selected [stageFieldHigh sp w,stageFieldLow sp w,stageSeedLow sp w,stageSeedHigh sp w,stageMaskHigh sp w,stageMaskLow sp w,returnSeedHigh sp w,returnMaskHigh sp w,returnMaskLow sp w,returnSeedLow sp w,returnFieldHigh sp w,returnFieldLow sp w] [] (tag sp w) w i hi
  intro t ht
  simp only [List.not_mem_nil] at ht

theorem inner_residue (sp : Nat) (w : State) (i : Nat) (hi : i < 128) :
    (moved sp w).memory (sp+i) = w.memory (sp+i) := by
  apply PV_EVH_StackStores.outside_all
  intro t ht
  change t ∈ [stageFieldHigh sp w,stageFieldLow sp w,stageSeedLow sp w,stageSeedHigh sp w,stageMaskHigh sp w,stageMaskLow sp w,returnSeedHigh sp w,returnMaskHigh sp w,returnMaskLow sp w,returnSeedLow sp w,returnFieldHigh sp w,returnFieldLow sp w,tag sp w] at ht
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Outside,stageFieldHigh,stageFieldLow,stageSeedLow,stageSeedHigh,stageMaskHigh,stageMaskLow,returnSeedHigh,returnMaskHigh,returnMaskLow,returnSeedLow,returnFieldHigh,returnFieldLow,tag,result,mask,caller]
    omega

theorem mask_residue (sp : Nat) (w : State) (i : Nat) (hi : i < 32) :
    (moved sp w).memory (mask sp+i) = w.memory (mask sp+i) := by
  apply PV_EVH_StackStores.outside_all
  intro t ht
  change t ∈ [stageFieldHigh sp w,stageFieldLow sp w,stageSeedLow sp w,stageSeedHigh sp w,stageMaskHigh sp w,stageMaskLow sp w,returnSeedHigh sp w,returnMaskHigh sp w,returnMaskLow sp w,returnSeedLow sp w,returnFieldHigh sp w,returnFieldLow sp w,tag sp w] at ht
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Outside,stageFieldHigh,stageFieldLow,stageSeedLow,stageSeedHigh,stageMaskHigh,stageMaskLow,returnSeedHigh,returnMaskHigh,returnMaskLow,returnSeedLow,returnFieldHigh,returnFieldLow,tag,result,mask,caller]
    omega

theorem outside_writes (sp p : Nat) (w : State)
    (hf : p < sp ∨ sp+232 ≤ p)
    (hr : p < result sp ∨ result sp+97 ≤ p) :
    (moved sp w).memory p = w.memory p := by
  apply PV_EVH_StackStores.outside_all
  intro t ht
  change t ∈ [stageFieldHigh sp w,stageFieldLow sp w,stageSeedLow sp w,stageSeedHigh sp w,stageMaskHigh sp w,stageMaskLow sp w,returnSeedHigh sp w,returnMaskHigh sp w,returnMaskLow sp w,returnSeedLow sp w,returnFieldHigh sp w,returnFieldLow sp w,tag sp w] at ht
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Outside,stageFieldHigh,stageFieldLow,stageSeedLow,stageSeedHigh,stageMaskHigh,stageMaskLow,returnSeedHigh,returnMaskHigh,returnMaskLow,returnSeedLow,returnFieldHigh,returnFieldLow,tag,result,mask,caller]
    omega

#print axioms stageFieldHigh_byte
#print axioms stageFieldLow_byte
#print axioms stageSeedLow_byte
#print axioms stageSeedHigh_byte
#print axioms stageMaskHigh_byte
#print axioms stageMaskLow_byte
#print axioms returnSeedHigh_byte
#print axioms returnMaskHigh_byte
#print axioms returnMaskLow_byte
#print axioms returnSeedLow_byte
#print axioms returnFieldHigh_byte
#print axioms returnFieldLow_byte
#print axioms tag_byte
#print axioms inner_residue
#print axioms mask_residue
#print axioms outside_writes
end PV_EVH_EntropyReturnFootprint
