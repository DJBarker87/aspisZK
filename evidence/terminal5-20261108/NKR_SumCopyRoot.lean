import NKR_SumCopyAssociation
import RPv_FJk_CopyRawValue
import RPv_JGa_Copy
import NJB_DecodeInjective
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumCopyRoot
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open FIq_Native.pool_v1.pair_forest_copy_terminal
open NKR_SumCopyCollect (Lookups)

/-- Complete8cell carrier join to the SAME adopted legacy row. -/
theorem row (values weights : Array NQ 4#usize) (model : R0P.CopyRowExtension K)
 (hv : ∀ g,decode (NJB_ArrayCarrier.cell values g)=NKR_SumLegacyRows.values model g)
 (hw : ∀ g,decode (NJB_ArrayCarrier.cell weights g)=NKR_SumLegacyRows.weights model g) :
 FIw_CopyTransport.row (NKR_SumCopyTail.row values weights)=model := by
 apply R0P.CopyRowExtension.ext
 · funext i
   fin_cases i
   · simpa [FIw_CopyTransport.row,NKR_SumCopyTail.row,FIv_NativeArray.value,Array.make,NKR_SumLegacyRows.values] using hv ⟨0,by decide⟩
   · simpa [FIw_CopyTransport.row,NKR_SumCopyTail.row,FIv_NativeArray.value,Array.make,NKR_SumLegacyRows.values] using hv ⟨1,by decide⟩
 · funext i
   fin_cases i
   · simpa [FIw_CopyTransport.row,NKR_SumCopyTail.row,FIv_NativeArray.value,Array.make,NKR_SumLegacyRows.weights] using hw ⟨0,by decide⟩
   · simpa [FIw_CopyTransport.row,NKR_SumCopyTail.row,FIv_NativeArray.value,Array.make,NKR_SumLegacyRows.weights] using hw ⟨1,by decide⟩
 · funext i
   fin_cases i
   · simpa [FIw_CopyTransport.row,NKR_SumCopyTail.row,FIv_NativeArray.value,Array.make,NKR_SumLegacyRows.values] using hv ⟨2,by decide⟩
   · simpa [FIw_CopyTransport.row,NKR_SumCopyTail.row,FIv_NativeArray.value,Array.make,NKR_SumLegacyRows.values] using hv ⟨3,by decide⟩
 · funext i
   fin_cases i
   · simpa [FIw_CopyTransport.row,NKR_SumCopyTail.row,FIv_NativeArray.value,Array.make,NKR_SumLegacyRows.weights] using hw ⟨2,by decide⟩
   · simpa [FIw_CopyTransport.row,NKR_SumCopyTail.row,FIv_NativeArray.value,Array.make,NKR_SumLegacyRows.weights] using hw ⟨3,by decide⟩

/-- Complete218 raw Result equality:the deployed optimized tensor reference
and adopted emitted legacy body return the SAME active/residual carrier.
The native frame/input cuts and field laws are inherited by call structure;
every child Result,canonicality,and eight-channel row equality is derived.
No source-success,desired-output,operation-dictionary,or cohort equality is a
root premise. The only additional premises are reviewed metadata cuts. -/
theorem source (lookup : Lookups) (keys : NKR_SumCopyAssociation.Keys) (domain : NKR_SumTagPermutation.Domain)
 (permutation : NKR_SumTagPermutation.Cut) (metadata : NKR_SumTagAssociation.Cut domain)
 (s : Selectors) (openings : Array NQ 16#usize) (helper lambda chi : NQ) (append : U64)
 (variant : PoolV1PairForestCompiledVariantV1)
 (ho : FIw_ArrayValue.canonical openings) (hhelper : Canon helper) (hlambda : Canon lambda) (hchi : Canon chi)
 (hh : FIw_ArrayValue.canonical s.high) (hl : FIw_ArrayValue.canonical s.low) :
 NKR_SumCopyInvocation.reference lookup s openings helper lambda chi append variant=
 evaluate_with_selectors openings helper s lambda chi append variant := by
 obtain ⟨old,oldCall,oldResCanon,oldActiveCanon⟩ := JGa_Copy.source openings helper s lambda chi append variant ho hhelper hh hl hlambda hchi
 obtain ⟨patterns,patternCall,cp,oldActiveCall,_,_,oldValue⟩ := FJk_CopyRawValue.value
  openings helper s lambda chi append variant old ho hhelper hh hl hlambda hchi oldCall
 obtain ⟨scratch,values,weights,collectCall,finishCall,cv,cw,veq,weq⟩ :=
  NKR_SumCopyAssociation.source lookup keys domain permutation metadata s patterns append variant hh hl cp
 obtain ⟨active,residual,scaled,activeCall,ca,residualCall,cr,mulCall,cs,tailCall,residualValue,scaledValue⟩ :=
  NKR_SumCopyTail.source s values weights helper chi hh hl cv cw hhelper hchi
 have sameRow := row values weights (FJk_CopyFullFold.model s patterns append variant) veq weq
 have sameActive : active=old.active := Result.ok.inj (activeCall.symm.trans oldActiveCall)
 have sameResidualValue : decode scaled=decode old.residual := by
  rw [scaledValue,FIw_CopyTransport.value_exact,sameRow,sameActive]
  exact oldValue.symm
 have sameResidual : scaled=old.residual := NJB_DecodeInjective.qm _ _ cs oldResCanon sameResidualValue
 have sameOut : ({residual:=scaled,active:=active} : PoolV1PairForestCompiledCopyTerminalV1)=old := by
  cases old
  simp only at sameActive sameResidual
  cases sameActive
  cases sameResidual
  rfl
 have refCall : NKR_SumCopyInvocation.reference lookup s openings helper lambda chi append variant=
  ok ({residual:=scaled,active:=active} : PoolV1PairForestCompiledCopyTerminalV1) := by
  simp only [NKR_SumCopyInvocation.reference,patternCall,collectCall,finishCall,bind_tc_ok]
  change NKR_SumCopyTail.reference s values weights helper chi=ok {residual:=scaled,active:=active}
  exact tailCall
 rw [sameOut] at refCall
 exact refCall.trans oldCall.symm

#print axioms row
#print source
#print axioms source
end AspisR1.NKR_SumCopyRoot
end
