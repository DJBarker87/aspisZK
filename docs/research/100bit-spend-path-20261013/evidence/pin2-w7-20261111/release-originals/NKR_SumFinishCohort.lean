import NKR_SumFinishInvocation
import NKR_SumFinishExpanded
import NKR_SumPatternMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumFinishCohort
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NKR_SumFinishData
open NKR_SumFinishInvocation (Selectors Scratch Patterns tagValues weightValues lowValues zero4 zero26)

def tag (s : Selectors) (c : Fin 30) : K := NJL_TagMeaning.model s (NJL_TagData.indices c)
def low (s : Selectors) (c : Fin 30) : K := decode (NJB_ArrayCarrier.cell s.low (NKR_SumFinishData.low c))
def baseValues (s : Selectors) (g : Fin 4) : K :=
 ((List.finRange 30).map (fun c=>if group c=g then tag s c*low s c else 0)).sum
def baseWeights (scratch : Scratch) (s : Selectors) (g : Fin 4) : K :=
 ((List.finRange 30).map (fun c=>if group c=g then decode (weightValues scratch c)*low s c else 0)).sum
def coefficient (scratch : Scratch) (s : Selectors) (j : Fin 26) : K :=
 ((List.finRange 43).map (fun c=>if pOut c=j then
  decode (NJB_ArrayCarrier.cell scratch (NKR_SumFinishPattern.scratchIndex c))*
  decode (NJB_ArrayCarrier.cell s.low (pLow c)) else 0)).sum
def values (scratch : Scratch) (s : Selectors) (terms : Patterns) (g : Fin 4) : K :=
 baseValues s g+NJL_PatternMeaning.dot (fun i=>decode (NJB_ArrayCarrier.cell terms i)) (coefficient scratch s) g

/-- Complete220 returned tuple equals its unbatched coordinate cohort:
30tag/weight coordinates,43pattern coefficients,then219's actual sparse
pattern basis. Native/source invocation traces remain available from the
same predecessor root. No returned output or cohort equality is assumed. -/
theorem source (scratch : Scratch) (s : Selectors) (terms : Patterns)
 (hsc : FIw_ArrayValue.canonical scratch) (hh : FIw_ArrayValue.canonical s.high)
 (hl : FIw_ArrayValue.canonical s.low) (ht : FIw_ArrayValue.canonical terms) :
 ∃ (outValues outWeights : Array NQ 4#usize),
 NKR_SumFinishInvocation.reference scratch s terms=ok (outValues,outWeights) ∧
 FIw_ArrayValue.canonical outValues ∧ FIw_ArrayValue.canonical outWeights ∧
 (∀ g,decode (NJB_ArrayCarrier.cell outValues g)=values scratch s terms g) ∧
 (∀ g,decode (NJB_ArrayCarrier.cell outWeights g)=baseWeights scratch s g) := by
 obtain ⟨dot,coefficients,finished,tc,_,_,_,_,_,_,call,_,dotMeaning,coeffMeaning,cf,cw,finalValue⟩ :=
  NKR_SumFinishInvocation.source scratch s terms hsc hh hl ht
 have tagValue (c : Fin 30) : decode (tagValues s c)=tag s c := (tc c).2.2
 have dv (g : Fin 4) : decode (dot.1 g)=baseValues s g := by
  have v := congrArg (fun state : NKR_SumFinishMeaning.ModelState=>state.1 g) dotMeaning
  have v' := v.trans (NKR_SumFinishAlgebra.values (tagValues s) (weightValues scratch) (lowValues s)
   NKR_SumFinishFold.order (NKR_SumFinishMeaning.decoded (zero4,zero4)) g)
  change decode (dot.1 g)=decode FIq_Native.field.QM31.ZERO+_ at v'
  rw [FIv_NativeValue.zero.2,zero_add] at v'
  rw [NKR_SumFinishExpanded.group_value] at v'
  simpa only [baseValues,tagValue,low,lowValues] using v'
 have dw (g : Fin 4) : decode (dot.2 g)=baseWeights scratch s g := by
  have v := congrArg (fun state : NKR_SumFinishMeaning.ModelState=>state.2 g) dotMeaning
  have v' := v.trans (NKR_SumFinishAlgebra.weights (tagValues s) (weightValues scratch) (lowValues s)
   NKR_SumFinishFold.order (NKR_SumFinishMeaning.decoded (zero4,zero4)) g)
  change decode (dot.2 g)=decode FIq_Native.field.QM31.ZERO+_ at v'
  rw [FIv_NativeValue.zero.2,zero_add] at v'
  rw [NKR_SumFinishExpanded.group_value] at v'
  simpa only [baseWeights,low,lowValues] using v'
 have pc (j : Fin 26) : decode (coefficients j)=coefficient scratch s j := by
  have v := congrFun coeffMeaning j
  have v' := v.trans (NKR_SumPatternMeaning.source
   (fun i=>decode (NJB_ArrayCarrier.cell scratch i)) (fun i=>decode (NJB_ArrayCarrier.cell s.low i))
   (List.finRange 43) (NJB_StateUpdates.decoded zero26) j)
  change decode (coefficients j)=decode FIq_Native.field.QM31.ZERO+_ at v'
  rw [FIv_NativeValue.zero.2,zero_add] at v'
  exact v'
 refine ⟨NJB_ArrayCarrier.array finished,NJB_ArrayCarrier.array dot.2,call,
  NJB_ArrayCarrier.canonical_array _ cf,NJB_ArrayCarrier.canonical_array _ cw,?_,?_⟩
 · intro g
   rw [NJB_ArrayCarrier.cell_array,finalValue,dv]
   have cp : (fun i=>decode (coefficients i))=coefficient scratch s := funext pc
   rw [cp]
   rfl
 · intro g
   rw [NJB_ArrayCarrier.cell_array]
   exact dw g

#print source
#print axioms source
end AspisR1.NKR_SumFinishCohort
end
