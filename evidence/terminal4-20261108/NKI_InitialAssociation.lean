import NKI_InitialTotal
import NKI_InitialFactor
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_InitialAssociation
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (canonical)
open NKI_InitialPrefix (Public Openings Selectors Tail)
def reference (p : Public) (o : Openings) (s : Selectors) : Result (Array field.QM31 16#usize × Array field.QM31 16#usize) := do
 let t←NKI_InitialPrefix.run p o s
 let absorption←NJB_Absorption.reference t.low t.fixed t.two t.eight t.nodes o.z
 ok (t.initial,absorption)
/-- Complete returned pair/source/cohort association for the fixed deployed
factored absorption child227 at SAME prefix outputs. SUPPORT until typed
native prefix/window certificates are composed at the260 root. -/
theorem source (p : Public) (o : Openings) (s : Selectors)
 (hz : canonical o.z) (hh : canonical s.high) (hl : canonical s.low) :
 ∃ (t : Tail) (absorption : Array field.QM31 16#usize),
 NKI_InitialPrefix.run p o s=ok t ∧ NKI_InitialTotal.Canonical t ∧
 NJB_Absorption.reference t.low t.fixed t.two t.eight t.nodes o.z=ok absorption ∧
 pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal t.low t.fixed t.two t.eight t.nodes o.z=ok absorption ∧
 canonical absorption ∧ reference p o s=ok (t.initial,absorption) ∧
 pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption p o s=ok (t.initial,absorption) := by
 obtain ⟨t,ct,ht⟩ := WP.spec_imp_exists (NKI_InitialTotal.source p o s hz hh hl)
 obtain ⟨r,caches,scales,ys,absorption,cut,clauses,trace,eq,ha,ca,co⟩ := NJL_AbsorptionInvocation.source t.low t.fixed t.two t.eight t.nodes o.z ht.2.1 ht.2.2.1 ht.2.2.2.1 ht.2.2.2.2.1 ht.2.2.2.2.2 hz
 refine ⟨t,absorption,ct,ht,ca,co,ha,?_,?_⟩
 · simp only [reference,ct,ca,bind_tc_ok]
 · rw [←NKI_InitialFactor.source]
   simp only [NKI_InitialFactor.literal,ct,co,bind_tc_ok]
#print source
#print axioms source
end AspisR1.NKI_InitialAssociation
end
