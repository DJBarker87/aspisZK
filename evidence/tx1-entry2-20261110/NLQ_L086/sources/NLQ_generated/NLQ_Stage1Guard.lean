import NLQ_Stage1Parent
set_option autoImplicit false
noncomputable section
namespace NLQ_Stage1Guard
open Aeneas Aeneas.Std Result AspisR1 NLQ_Stage1State NLQ_Stage1Parent
/-- Rejection occurs before any account length check, borrow, snapshot or
child call. The attempted instruction comparisons remain in the prepend. -/
theorem rejected (e : S2W_D189Entry.Entry) (ops : AdapterRw.Ops) (p : Key)
 (d : Slice U8) (n : Nat) (a0 a1 a2 : Result Unit) (bad : ¬ NLQ_Route.Tx1 d) :
 G e ops p d n a0 a1 a2 =
 ⟨.ok (.Err .InvalidInstructionData),initial e,
  [.instruction (initial e) d 10#u8 false,.instruction (initial e) d 11#u8 false]⟩ := by
 have ten : d.val≠[3#u8,10#u8] := fun h => bad (Or.inl h)
 have eleven : d.val≠[3#u8,11#u8] := fun h => bad (Or.inr h)
 simp [G,ten,eleven]
/-- Wrong account count preserves the whole initial SDK/owned state and
never evaluates an allocator or child, for either admitted TX1 tag. -/
theorem wrong_count (e : S2W_D189Entry.Entry) (ops : AdapterRw.Ops) (p : Key)
 (d : Slice U8) (n : Nat) (a0 a1 a2 : Result Unit) (bad : n≠3) :
 (G e ops p d n a0 a1 a2).result=.ok (.Err .InvalidInstructionData) ∧
 (G e ops p d n a0 a1 a2).post=initial e := by
 unfold G
 split
 · simp [prepend,count,bad]
 · split <;> simp [prepend,count,bad]
#print rejected
#print axioms rejected
#print axioms wrong_count
end NLQ_Stage1Guard
