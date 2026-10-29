import R1Z.PV_OWNN_SourceDense
set_option autoImplicit false
noncomputable section
namespace PV_SKWB_OWNM
open R1Z R1Z.PV_OWNM_V239 Aeneas Aeneas.Std Result
abbrev K := PV_OWNK_ConcreteDecoder.K
abbrev decode := PV_OWNK_ConcreteDecoder.decode
abbrev zero := PV_OWNI_RawOps.zero
abbrev one := PV_OWNI_RawOps.one
abbrev source222 := PV_OWNN_SourceDense.source222
def point : List Q := List.replicate 10 one
def wirePoints (p : List Q) : List (List Q) := [p,p.reverse,p]
def columns : List (List Q) := [List.replicate 1024 one,List.replicate 1024 zero]
def input (site : Site) : Input := ⟨⟨[1],[[2]],1,2,3⟩,site,point,columns⟩
def reconstruct (_ : Public) : List Q := point
def resource (i : Input) (_ : List Q) (lane : Nat) : ResourceExit Nat :=
 .ready (lane+1) (plan PV_OWNI_Scanner.boolean (calls wirePoints i) [])
def native (i : Input) (p : List Q) (lane : Nat) : Execution K Nat :=
 attach (resource i p lane)
  (do let v ← source222 p (i.columns[lane]?.getD []); ok (v.map decode))
theorem actual_input (site : Site) : PV_OWNM_Link_ActualInput wirePoints (input site) := by
 have ho : Canon one := PV_OWNK_ConcreteDecoder.decoder.one_canon
 have hz : Canon zero := PV_OWNK_ConcreteDecoder.decoder.zero_canon
 constructor
 · exact List.length_replicate
 constructor
 · intro p hp
   simp only [wirePoints,List.mem_cons,List.mem_singleton] at hp
   rcases hp with h|h|h <;> subst p <;>
    simp [input,point,List.mem_replicate,ho]
 · intro c hc q hq
   simp only [input,columns,List.mem_cons,List.mem_singleton] at hc
   rcases hc with h|h <;> subst c
   · have h := (List.mem_replicate.mp hq).2; subst q; exact ho
   · have h := (List.mem_replicate.mp hq).2; subst q; exact hz

theorem owned (i : Input) :
 PV_OWNM_Link_OwnedPublicPlan decode source222 wirePoints PV_OWNI_Scanner.boolean
  native resource [] i := by
 constructor
 · intro p hp lane c hc
   simp only [native,hc,Option.getD_some]
 · intro p hp lane c hc
   rfl
/-- Concrete decoder and the proved scalar source law, on both sides and both sites.
Nonempty columns and wire points make every operational link active. -/
theorem satisfiable : ∃ pair : Input × Input,
 PV_OWNM_Link_ActualInput wirePoints pair.1 ∧
 PV_OWNM_Link_ActualInput wirePoints pair.2 ∧
 PV_OWNM_Link_SourceDense decode zero source222 ∧
 PV_OWNM_Link_Transcript879 reconstruct pair.1 ∧
 PV_OWNM_Link_Transcript879 reconstruct pair.2 ∧
 PV_OWNM_Link_Transcript890 reconstruct pair.1 ∧
 PV_OWNM_Link_Transcript890 reconstruct pair.2 ∧
 PV_OWNM_Link_OwnedPublicPlan decode source222 wirePoints PV_OWNI_Scanner.boolean native resource [] pair.1 ∧
 PV_OWNM_Link_OwnedPublicPlan decode source222 wirePoints PV_OWNI_Scanner.boolean native resource [] pair.2 ∧
 pair.1.pubData = pair.2.pubData ∧ pair.1.site = pair.2.site ∧
 pair.1.columns.map List.length = pair.2.columns.map List.length := by
 refine ⟨(input .callback879,input .callback879),actual_input _,actual_input _,
  PV_OWNN_SourceDense.concrete_source_dense,?_,?_,?_,?_,owned _,owned _,rfl,rfl,rfl⟩
 all_goals intro h; rfl
/-- Final-site transcript reconstruction is active as well. -/
theorem final_links : PV_OWNM_Link_ActualInput wirePoints (input .final890) ∧
 PV_OWNM_Link_Transcript879 reconstruct (input .final890) ∧
 PV_OWNM_Link_Transcript890 reconstruct (input .final890) ∧
 PV_OWNM_Link_OwnedPublicPlan decode source222 wirePoints PV_OWNI_Scanner.boolean native resource [] (input .final890) := by
 exact ⟨actual_input _,(fun _ => rfl),(fun _ => rfl),owned _⟩
theorem nondegenerate (site : Site) : (input site).point.length = 10 ∧
 (wirePoints (input site).point).length = 3 ∧
 ((input site).columns.map List.length) = [1024,1024] := by
 simp only [input,point,wirePoints,columns,List.length_replicate,List.length_cons,
  List.length_nil,List.map_cons,List.map_nil]
 exact ⟨rfl,rfl,rfl⟩
#print axioms actual_input
#print axioms owned
#print axioms satisfiable
#print axioms final_links
#print axioms nondegenerate
end PV_SKWB_OWNM
