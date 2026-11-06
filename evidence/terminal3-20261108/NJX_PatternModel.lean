import NJX_PatternPacket
import RPv_FJk_PatternValues
import RPv_JGa_CopyPatterns
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_PatternModel
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

end AspisR1.NJX_PatternModel
end
