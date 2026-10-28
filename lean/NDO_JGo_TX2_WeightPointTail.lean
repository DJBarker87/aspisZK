import NDO_JGo_TX2_WeightData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_WeightPointTail
open Aeneas Aeneas.Std Result FIn_WeightsExtract JGo_TX2_WeightData
def minus7 : Q := ⟨⟨123619232#u32,1164402415#u32⟩,⟨1959602462#u32,809095634#u32⟩⟩
def minus6 : Q := ⟨⟨736800423#u32,1771886978#u32⟩,⟨1174221777#u32,2025396938#u32⟩⟩
def first : Array Q 10#usize := Array.make 10#usize [⟨⟨705343446#u32,1948609717#u32⟩,⟨871005084#u32,203308705#u32⟩⟩,⟨⟨528783666#u32,1672539309#u32⟩,⟨1274387717#u32,552414171#u32⟩⟩,⟨⟨1657509587#u32,287924440#u32⟩,⟨1819227394#u32,1192254731#u32⟩⟩,⟨⟨1142413086#u32,2006134641#u32⟩,⟨1686703278#u32,2011383024#u32⟩⟩,⟨⟨1106424694#u32,342809735#u32⟩,⟨1036886578#u32,305075687#u32⟩⟩,⟨⟨810819047#u32,1156380883#u32⟩,⟨768810467#u32,1018558903#u32⟩⟩,⟨⟨1410683225#u32,375596669#u32⟩,⟨973261870#u32,122086709#u32⟩⟩,⟨⟨123619232#u32,1164402415#u32⟩,⟨1959602462#u32,809095634#u32⟩⟩,⟨⟨454398981#u32,504493626#u32⟩,⟨2008082900#u32,1252680230#u32⟩⟩,⟨⟨2030227143#u32,1410410828#u32⟩,⟨1902035786#u32,62756635#u32⟩⟩]
theorem sub7 : field.QM31.sub field.QM31.ONE (alpha.val[7])=ok minus7 := by
  with_unfolding_all rfl
#print axioms sub7
theorem sub6 : field.QM31.sub field.QM31.ONE (first.val[6])=ok minus6 := by
  with_unfolding_all rfl
#print axioms sub6
theorem update7 : Array.update alpha 7#usize minus7=ok first := by rfl
#print axioms update7
theorem update6 : Array.update first 6#usize minus6=ok absorption := by rfl
#print axioms update6
end AspisR1.JGo_TX2_WeightPointTail
end
