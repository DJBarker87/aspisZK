import NKI_InitialDomains
import NKI_InitialLaneResults
import NKI_InitialReads
import NKI_InitialCuts
import NKI_InitialAssociation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_InitialRoot
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical)
open NKI_InitialPrefix (Public Openings Selectors)
open NKI_InitialInvocation (Locals)
/-- Complete260 candidate: all actual scalar/cache/array Results, all native
cut arguments and full16+16return carrier; SAME closed/candidate227 call.
Only the root's actual input domains remain. -/
theorem source (p : Public) (o : Openings) (s : Selectors)
 (hz : canonical o.z) (hh : canonical s.high) (hl : canonical s.low) :
 ∃ (l : Locals) (absorption : Array NQ 16#usize),
 NKI_InitialInvocation.Clauses p o s l ∧ NKI_InitialTrace.Canonical l ∧ NKI_InitialReads.Reads s l ∧
 NJB_PreparedLaws.Domain l.full l.full_initial_selector ∧ NJB_PreparedLaws.Domain l.full_or_rate l.q12 ∧
 (∀ i : Fin 16,field.PreparedQm31Multiplier.mul (NKI_InitialLaneResults.cache l.full_or_rate l.full i) (NJB_ArrayCarrier.cell o.z i)=ok (NJB_ArrayCarrier.cell l.initial i)) ∧
 NKI_InitialCuts.Cut p o s l absorption (NKI_InitialCuts.observations p o s l absorption) ![12,2,12,9,16,4,1] ∧
 NJB_Absorption.reference l.q38 l.fixed l.chunk_two1 l.chunk_eight1 l.nodes o.z=ok absorption ∧
 NKI_InitialAssociation.reference p o s=ok (l.initial2,absorption) ∧
 pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption p o s=ok (l.initial2,absorption) ∧
 canonical l.initial2 ∧ canonical absorption := by
 obtain ⟨l,cl,hc⟩ := WP.spec_imp_exists (NKI_InitialTrace.source p o s hz hh hl)
 have calls:=NKI_InitialTraceFactor.clauses p o s l cl
 have domains:=NKI_InitialDomains.source p o s l calls hc
 have prefix : NKI_InitialPrefix.run p o s=ok (NKI_InitialInvocation.output l) := by
  rw [←NKI_InitialTraceFactor.source,cl,bind_tc_ok]
 -- Remaining full-source scalar, frame and227 association is constructed from
 -- this SAME prefix, never selected independently.
 obtain ⟨t,absorption,ct,ht,ca,co,ha,cr,cs⟩ := NKI_InitialAssociation.source p o s hz hh hl
 have same : t=NKI_InitialInvocation.output l := Result.ok.inj (ct.symm.trans prefix)
 subst t
 have rateCanonical : FIv_NativeValue.Canon l.q12 := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
 have fullCanonical : FIv_NativeValue.Canon l.full_initial_selector := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
 have initialCall := calls.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
 refine ⟨l,absorption,calls,hc,NKI_InitialReads.source p o s l calls,domains.1,domains.2,?_,NKI_InitialCuts.source p o s l absorption calls,ca,cr,cs,ht.1,ha⟩
 exact NKI_InitialLaneResults.source l.q12 l.full_initial_selector l.full_or_rate l.full o l.initial rateCanonical fullCanonical domains.2 domains.1 hz initialCall
#print source
#print axioms source
end AspisR1.NKI_InitialRoot
end
