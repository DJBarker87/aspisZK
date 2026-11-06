import NLQ_Stage1Parent
set_option autoImplicit false
noncomputable section
namespace NLQ_Stage1Body
open Aeneas Aeneas.Std Result AspisR1 NLQ_Stage1State NLQ_Stage1Parent
/-- Complete body observations at BOTH admitted instructions; the snapshot
prepend and abort post-state are retained, with no successful-child premise. -/
theorem ten (e : S2W_D189Entry.Entry) (ops : AdapterRw.Ops) (p : Key)
 (a0 a1 a2 : Result Unit) :
 G e ops p NJD_Prefixes.ten 3 a0 a1 a2 =
 let body := NLQ_Stage1Fold.G e ops p NJD_Prefixes.ten a0 a1 a2
 ⟨body.result,body.post,[.instruction (initial e) NJD_Prefixes.ten 10#u8 true,
  .count (initial e) 3]++body.events.map Event.body⟩ := by
 simp [G,count,prepend,NJD_Prefixes.ten]
theorem eleven (e : S2W_D189Entry.Entry) (ops : AdapterRw.Ops) (p : Key)
 (a0 a1 a2 : Result Unit) :
 G e ops p NJD_Prefixes.eleven 3 a0 a1 a2 =
 let body := NLQ_Stage1Fold.G e ops p NJD_Prefixes.eleven a0 a1 a2
 ⟨body.result,body.post,[.instruction (initial e) NJD_Prefixes.eleven 10#u8 false,
  .instruction (initial e) NJD_Prefixes.eleven 11#u8 true,
  .count (initial e) 3]++body.events.map Event.body⟩ := by
 simp [G,count,prepend,NJD_Prefixes.eleven]
theorem result (e : S2W_D189Entry.Entry) (ops : AdapterRw.Ops) (p : Key)
 (d : Slice U8) (a0 a1 a2 : Result Unit) (tx1 : NLQ_Route.Tx1 d) :
 (G e ops p d 3 a0 a1 a2).result=(NLQ_Stage1Fold.G e ops p d a0 a1 a2).result := by
 rcases tx1 with h | h
 · have eq : d=NJD_Prefixes.ten := Subtype.ext h
   subst d; rw [ten]
 · have eq : d=NJD_Prefixes.eleven := Subtype.ext h
   subst d; rw [eleven]
#print ten
#print eleven
#print axioms ten
#print axioms eleven
#print axioms result
end NLQ_Stage1Body
