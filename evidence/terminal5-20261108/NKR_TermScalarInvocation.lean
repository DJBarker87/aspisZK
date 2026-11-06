import NKR_TermScalar
import NIH_SelectorRow
import NJB_ArrayReads
import NJB_StubLaws
import NHU_Preweighted
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_TermScalarInvocation
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open NKI_InitialPrefix (Public Openings Selectors)
open pool_v1.pair_forest_semantic_terminal
abbrev Packed := Array NQ 24#usize
def rows : Fin 4 → Usize := ![44#usize,508#usize,460#usize,1010#usize]
def amount (pub : Public) : U32 := core.option.Option.unwrap_or pub.withdrawal_amount 0#u32
structure Packet (pub : Public) (o : Openings) (s : Selectors) (before : Packed) where
 difference : NQ
 selected : Fin 4 → NQ
 withdrawalDifference : NQ
 products : Fin 4 → NQ
 scalars : Array NQ 2#usize
 out : Packed
 asset_sub : field.QM31.sub (NJB_ArrayCarrier.cell o.z ⟨1,by decide⟩) (FIw_ScalarArithmetic.lifted pub.asset_id)=ok difference
 row_calls : ∀ g,s.row (rows g)=ok (selected g)
 amount_sub : field.QM31.sub (NJB_ArrayCarrier.cell o.z ⟨10,by decide⟩) (FIw_ScalarArithmetic.lifted (amount pub))=ok withdrawalDifference
 product_calls : ∀ g,field.QM31.mul (selected g) (if g.val=3 then withdrawalDifference else difference)=ok (products g)
 scalar_call : scalar_lanes pub.variant (core.option.Option.is_some pub.withdrawal_amount) (products 0) (products 1) (products 2) (products 3)=ok scalars
 packed_call : add_preweighted before 92#usize scalars=ok out
 differenceCanonical : Canon difference
 selectedCanonical : ∀ g,Canon (selected g)
 withdrawalCanonical : Canon withdrawalDifference
 productsCanonical : ∀ g,Canon (products g)
 scalarsCanonical : canonical scalars
 canonical : canonical out
/-- Exact14call261 scalar/preweighted92 source invocation. All four row
selectors, products,258variant branch and230full24reply are derived here. -/
theorem source (pub : Public) (o : Openings) (s : Selectors) (before : Packed)
 (hz : canonical o.z) (hh : canonical s.high) (hl : canonical s.low) (hb : canonical before)
 (ha : pub.asset_id.val<2147483647) (hm : (amount pub).val<2147483647) :
 ∃ p : Packet pub o s before,FIw_ScalarSuffix.run pub o s before=ok p.out := by
 have az:=FIw_ScalarArithmetic.lift_value pub.asset_id ha
 have mz:=FIw_ScalarArithmetic.lift_value (amount pub) hm
 obtain ⟨difference,dc,cd,_⟩:=NJB_StubLaws.qm_sub (NJB_ArrayCarrier.cell o.z ⟨1,by decide⟩) (FIw_ScalarArithmetic.lifted pub.asset_id) (NJB_ArrayCarrier.canonical_cell o.z hz _) az.1
 have rbound (g : Fin 4) : (rows g).val<1024 := by fin_cases g <;> decide
 choose selected rowsCall selectedCanonical value using (fun g : Fin 4=>NIH_SelectorRow.result s (rows g) (rbound g) hh hl)
 obtain ⟨withdrawalDifference,wc,cw,_⟩:=NJB_StubLaws.qm_sub (NJB_ArrayCarrier.cell o.z ⟨10,by decide⟩) (FIw_ScalarArithmetic.lifted (amount pub)) (NJB_ArrayCarrier.canonical_cell o.z hz _) mz.1
 have differences (g : Fin 4) : Canon (if g.val=3 then withdrawalDifference else difference) := by split <;> assumption
 choose products productCall productsCanonical productValue using (fun g : Fin 4=>NJB_StubLaws.qm_mul (selected g) (if g.val=3 then withdrawalDifference else difference) (selectedCanonical g) (differences g))
 obtain ⟨scalars,sc,cs⟩:=JFy_Scalars.source pub.variant (core.option.Option.is_some pub.withdrawal_amount) (products 0) (products 1) (products 2) (products 3) (productsCanonical 0) (productsCanonical 1) (productsCanonical 2) (productsCanonical 3)
 obtain ⟨out,pc,co,_⟩:=NHU_Preweighted.result before 92#usize scalars (by decide) (by decide) hb cs
 let p : Packet pub o s before:=⟨difference,selected,withdrawalDifference,products,scalars,out,dc,rowsCall,wc,productCall,sc,pc,cd,selectedCanonical,cw,productsCanonical,cs,co⟩
 have z1 : Array.index_usize o.z 1#usize=ok (NJB_ArrayCarrier.cell o.z ⟨1,by decide⟩):=NJB_ArrayReads.read o.z 1#usize (by decide)
 have z10 : Array.index_usize o.z 10#usize=ok (NJB_ArrayCarrier.cell o.z ⟨10,by decide⟩):=NJB_ArrayReads.read o.z 10#usize (by decide)
 refine ⟨p,?_⟩
 change FIw_ScalarSuffix.run pub o s before=ok out
 unfold FIw_ScalarSuffix.run VALUE_AUXILIARY_BLOCK
 erw [z1,bind_tc_ok,FIw_ScalarArithmetic.lift_run,bind_tc_ok,dc,bind_tc_ok]
 simp only [FIw_ScalarIndices.mul2,FIw_ScalarIndices.add44,FIw_ScalarIndices.mul31,FIw_ScalarIndices.add508,
  FIw_ScalarIndices.mul28,FIw_ScalarIndices.add460,FIw_ScalarIndices.mul63,FIw_ScalarIndices.add1010,bind_tc_ok]
 have r0 : s.row 44#usize=ok (selected 0):=rowsCall 0
 have r1 : s.row 508#usize=ok (selected 1):=rowsCall 1
 have r2 : s.row 460#usize=ok (selected 2):=rowsCall 2
 have r3 : s.row 1010#usize=ok (selected 3):=rowsCall 3
 have m0 : field.QM31.mul (selected 0) difference=ok (products 0):=productCall 0
 have m1 : field.QM31.mul (selected 1) difference=ok (products 1):=productCall 1
 have m2 : field.QM31.mul (selected 2) difference=ok (products 2):=productCall 2
 have m3 : field.QM31.mul (selected 3) withdrawalDifference=ok (products 3):=productCall 3
 erw [r0,bind_tc_ok,m0,bind_tc_ok,r1,bind_tc_ok,m1,bind_tc_ok,r2,bind_tc_ok,m2,bind_tc_ok]
 change (do let q←s.row 1010#usize
            let z←Array.index_usize o.z 10#usize
            let target←lift_m31 (amount pub)
            let difference←field.QM31.sub z target
            let withdrawal←field.QM31.mul q difference
            let scalars←scalar_lanes pub.variant (core.option.Option.is_some pub.withdrawal_amount) (products 0) (products 1) (products 2) withdrawal
            add_preweighted before 92#usize scalars)=ok out
 erw [r3,bind_tc_ok,z10,bind_tc_ok,FIw_ScalarArithmetic.lift_run,bind_tc_ok,wc,bind_tc_ok,m3,bind_tc_ok,sc,bind_tc_ok,pc]
#print source
#print axioms source
end AspisR1.NKR_TermScalarInvocation
end
