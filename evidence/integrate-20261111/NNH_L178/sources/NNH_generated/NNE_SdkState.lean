import NNE_SdkCells
import NLF_ParentModel
set_option autoImplicit false
namespace NNE_SdkState
/-- SDK fields absent from RSL (including lamports/rent) remain ambient inputs.
The adapter never sets them to a constant or drops them from the full world. -/
def cell (money : Nat → Nat) (s : RSL.SdkState) (i : Nat) :
 NLF_RefCell.Cell NLF_SdkModel.Payload :=
 ⟨⟨(s.cells i).payload,money i⟩,(s.cells i).readers,(s.cells i).writer⟩
def state (accounts : Nat → NLF_SdkModel.Account) (money : Nat → Nat)
 (s : RSL.SdkState) : NLF_SdkModel.State := ⟨accounts,cell money s⟩
def parent (accounts : Nat → NLF_SdkModel.Account) (money : Nat → Nat)
 (s : RSL.SdkState) (events : List NLF_ParentModel.Event) : NLF_ParentModel.Parent :=
 ⟨state accounts money s,s.next,events⟩
def Fresh (s : RSL.SdkState) : Prop :=
 ∀ i t, ((s.cells i).writer = some t ∨ t ∈ (s.cells i).readers) → t < s.next

theorem fresh_of_below (accounts : Nat → NLF_SdkModel.Account) (money : Nat → Nat)
 (s : RSL.SdkState) :
 NLF_ParentModel.Below (state accounts money s) s.next ↔ Fresh s := Iff.rfl

theorem fresh_token (s : RSL.SdkState) (h : Fresh s) (i : Nat) :
 s.next ∉ (s.cells i).readers ∧ (s.cells i).writer ≠ some s.next := by
 constructor
 · intro hh; exact Nat.lt_irrefl _ (h i s.next (Or.inr hh))
 · intro hh; exact Nat.lt_irrefl _ (h i s.next (Or.inl hh))

theorem put (accounts : Nat → NLF_SdkModel.Account) (money : Nat → Nat)
 (s : RSL.SdkState) (i : Nat) (c : RSL.Cell) :
 state accounts money (s.put i c) =
 NLF_SdkModel.put (state accounts money s) i ⟨⟨c.payload,money i⟩,c.readers,c.writer⟩ := by
 unfold state NLF_SdkModel.put
 congr 1
 funext j
 by_cases h : j = i
 · subst j; simp [cell,RSL.SdkState.put]
 · simp [cell,RSL.SdkState.put,h]

theorem deref (accounts : Nat → NLF_SdkModel.Account) (money : Nat → Nat)
 (s : RSL.SdkState) (a : RSL.AccountInfo) (t : Nat) (k : RSL.Kind) :
 (NLF_SdkModel.deref (state accounts money s) ⟨a.cell,t,NNE_SdkCells.kind k⟩).bytes =
 RSL.payload a s := rfl

theorem ambient_frame (accounts : Nat → NLF_SdkModel.Account) (money : Nat → Nat)
 (s : RSL.SdkState) (i : Nat) :
 (state accounts money s).accounts = accounts ∧
 ((state accounts money s).cells i).payload.money = money i := ⟨rfl,rfl⟩
#print axioms fresh_of_below
#print axioms fresh_token
#print axioms put
#print axioms deref
#print axioms ambient_frame
end NNE_SdkState
