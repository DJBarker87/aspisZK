import NJX_InitialVariant
import NJB_PreparedLaws
import NJB_ArrayCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_InitialPrologue
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIv_PreparedNew (NP)
open NJX_InitialVariant (Variant)
abbrev Selectors := FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors
def high (s : Selectors) (i : Fin 64) : NQ := NJB_ArrayCarrier.cell s.high ⟨i.val,by have h:=i.isLt;scalar_tac⟩
def low0 (s : Selectors) : NQ := NJB_ArrayCarrier.cell s.low 0
structure Packet (s : Selectors) (v : Variant) (nodes : NQ) where
 common : NQ
 transfer : NQ
 fixed : NQ
 eight : NQ
 two : NQ
 common1 : NQ
 common2 : NQ
 full1 : NQ
 full2 : NQ
 fullValue : NQ
 rateValue : NQ
 bothValue : NQ
 full : NP
 both : NP
 add1 : FIq_Native.field.QM31.add (high s 0) (high s 1)=ok common1
 add2 : FIq_Native.field.QM31.add common1 (high s 25)=ok common2
 add3 : FIq_Native.field.QM31.add common2 (high s 30)=ok common
 variant_call : FIq_Native.pool_v1.pair_forest_semantic_terminal.initial_variant_selectors v (high s 27) (high s 28) (high s 29)=ok (transfer,fixed,eight,two)
 add4 : FIq_Native.field.QM31.add common transfer=ok full1
 add5 : FIq_Native.field.QM31.add full1 fixed=ok full2
 mul1 : FIq_Native.field.QM31.mul (low0 s) full2=ok fullValue
 mul2 : FIq_Native.field.QM31.mul (low0 s) nodes=ok rateValue
 new1 : FIq_Native.field.PreparedQm31Multiplier.new fullValue=ok full
 add6 : FIq_Native.field.QM31.add fullValue rateValue=ok bothValue
 new2 : FIq_Native.field.PreparedQm31Multiplier.new bothValue=ok both
 domain1 : NJB_PreparedLaws.Domain full fullValue
 domain2 : NJB_PreparedLaws.Domain both bothValue
 canonical : Canon transfer ∧ Canon fixed ∧ Canon eight ∧ Canon two ∧ Canon fullValue ∧ Canon bothValue
/-- Exact actual260 scalar/cache prefix after nodes; SUPPORT until the
node-child binding, native cuts, lane constructor and writes8/9 compose. -/
theorem source (s : Selectors) (v : Variant) (nodes : NQ)
 (hs : FIw_ArrayValue.canonical s.high) (hl : FIw_ArrayValue.canonical s.low) (hn : Canon nodes) :
 ∃ p : Packet s v nodes,True := by
 have hh : ∀ i,Canon (high s i) := fun i=>NJB_ArrayCarrier.canonical_cell s.high hs _
 have hlow : Canon (low0 s) := NJB_ArrayCarrier.canonical_cell s.low hl _
 obtain ⟨c1,cc1,hc1,_⟩ := NJB_StubLaws.qm_add _ _ (hh 0) (hh 1)
 obtain ⟨c2,cc2,hc2,_⟩ := NJB_StubLaws.qm_add _ _ hc1 (hh 25)
 obtain ⟨common,cc,hc,_⟩ := NJB_StubLaws.qm_add _ _ hc2 (hh 30)
 obtain ⟨t,f,eight,two,cv,ht,hf,he,hw⟩ := NJX_InitialVariant.source v _ _ _ (hh 27) (hh 28) (hh 29)
 obtain ⟨f1,cf1,hf1,_⟩ := NJB_StubLaws.qm_add _ _ hc ht
 obtain ⟨f2,cf2,hf2,_⟩ := NJB_StubLaws.qm_add _ _ hf1 hf
 obtain ⟨fv,cfv,hfv,_⟩ := NJB_StubLaws.qm_mul _ _ hlow hf2
 obtain ⟨rv,crv,hrv,_⟩ := NJB_StubLaws.qm_mul _ _ hlow hn
 obtain ⟨full,cf,df⟩ := NJB_PreparedLaws.new_result fv hfv
 obtain ⟨bv,cbv,hbv,_⟩ := NJB_StubLaws.qm_add _ _ hfv hrv
 obtain ⟨both,cb,db⟩ := NJB_PreparedLaws.new_result bv hbv
 exact ⟨⟨common,t,f,eight,two,c1,c2,f1,f2,fv,rv,bv,full,both,cc1,cc2,cc,cv,cf1,cf2,cfv,crv,cf,cbv,cb,df,db,ht,hf,he,hw,hfv,hbv⟩,True.intro⟩
#print source
#print axioms source
end AspisR1.NJX_InitialPrologue
end
