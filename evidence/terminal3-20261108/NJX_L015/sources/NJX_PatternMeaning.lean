import NJX_PatternPacket
import RPv_FJk_PatternValues
import RPv_JGa_CopyPatterns
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_PatternMeaning
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
/-- Mathematical eight-cell window; the natural offset is bounded by9. -/
def window (o : Fin 16 → K) (lambda : K) (start : Fin 9) : K :=
 (List.ofFn (fun i : Fin 8=>lambda^(i.val+1)*o ⟨start.val+i.val,by have:=start.isLt;have:=i.isLt;omega⟩)).sum
/-- Frozen14tail value on the actual openings and the four source windows. -/
def atoms (o : Fin 16 → K) (lambda : K) (i : Fin 21) : K :=
 if h : i.val<16 then o ⟨i.val,h⟩
 else if h2 : i.val<20 then window o lambda (NJX_PatternPacket.starts ⟨i.val-16,by omega⟩)
 else 1051521018

def model (o : Fin 16 → K) (lambda : K) (j : Fin 14) : K :=
 NJX_TailExpr.value lambda (atoms o lambda) (NJX_PatternTail.expr j)

/-- Eight-cell windows give the literal pattern polynomial, by finite symbolic
algebra. No concrete field value or large numeral normalization is evaluated. -/
theorem value (o : Fin 16 → K) (lambda : K) (j : Fin 14) :
 model o lambda j=R0P.copyPatternValuesLiteral o lambda j := by
 fin_cases j <;>
 simp [model,NJX_PatternTail.expr,NJX_TailExpr.value,atoms,window,NJX_PatternPacket.starts,
  List.ofFn_succ,R0P.copyPatternValuesLiteral,R0P.copyPatterns,
  R0P.copyPattern0,R0P.copyPattern1,R0P.copyPattern2,R0P.copyPattern3,
  R0P.copyPattern4,R0P.copyPattern5,R0P.copyPattern6,R0P.copyPattern7,
  R0P.copyPattern8,R0P.copyPattern9,R0P.copyPattern10,R0P.copyPattern11,
  R0P.copyPattern12,R0P.copyPattern13,R0P.copy_powers_eq] <;> ring
#print value
#print axioms value
end AspisR1.NJX_PatternMeaning
end
