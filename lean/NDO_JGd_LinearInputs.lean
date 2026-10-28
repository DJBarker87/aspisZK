import NDO_JGd_ExactWords
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_LinearInputs
open Aeneas Aeneas.Std Result
open JGd_ExactWords

def points : Array W 10#usize := ⟨[
  ((705343446,1948609717),(871005084,203308705)),
  ((528783666,1672539309),(1274387717,552414171)),
  ((1657509587,287924440),(1819227394,1192254731)),
  ((1142413086,2006134641),(1686703278,2011383024)),
  ((1106424694,342809735),(1036886578,305075687)),
  ((810819047,1156380883),(768810467,1018558903)),
  ((1410683225,375596669),(973261870,122086709)),
  ((2023864416,983081232),(187881185,1338388013)),
  ((454398981,504493626),(2008082900,1252680230)),
  ((2030227143,1410410828),(1902035786,62756635))],by rfl⟩

def point (i : Fin 10) : W := points.val[i.val]'(by simpa [points.property] using i.isLt)

theorem decoded (i : Fin 10) :
    ExtractedMaskLinearsExact.decodedPoint
      (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.point) i = value (point i) := by
  fin_cases i <;> rfl
#print axioms decoded
end AspisR1.JGd_LinearInputs
end
