import NMB_Stage1Parent
set_option autoImplicit false
noncomputable section
namespace NMB_Stage1Guards
open Aeneas Aeneas.Std Result AspisR1 NMB_Stage1Source NMB_Stage1Parent
theorem rejected (x : NMB_Input.Input) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8)
 (n : Nat) (a0 a1 a2 : Result Unit) (bad : ¬ NLQ_Route.Tx1 d) :
 NMB_Stage1Parent.G x ops p d n a0 a1 a2=
 ⟨.ok (.Err .InvalidInstructionData),initial x,
 [.instruction (initial x) d 10#u8 false,.instruction (initial x) d 11#u8 false]⟩ := by
 have ten : d.val≠[3#u8,10#u8] := fun h=>bad (Or.inl h)
 have eleven : d.val≠[3#u8,11#u8] := fun h=>bad (Or.inr h)
 simp [NMB_Stage1Parent.G,ten,eleven]
theorem wrong_count (x : NMB_Input.Input) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8)
 (n : Nat) (a0 a1 a2 : Result Unit) (bad : n≠3) :
 (NMB_Stage1Parent.G x ops p d n a0 a1 a2).result=.ok (.Err .InvalidInstructionData) ∧
 (NMB_Stage1Parent.G x ops p d n a0 a1 a2).post=initial x := by
 by_cases ten : d.val=[3#u8,10#u8]
 · simp [NMB_Stage1Parent.G,ten,prepend,count,bad]
 · by_cases eleven : d.val=[3#u8,11#u8] <;>
    simp [NMB_Stage1Parent.G,ten,eleven,prepend,count,bad]
#print rejected
#print wrong_count
#print axioms rejected
#print axioms wrong_count
end NMB_Stage1Guards
