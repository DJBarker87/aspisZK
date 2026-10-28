import NDO_JGl_WordProof
import NDO_JGl_NumericData
import NDO_JFu_PublicSemantic
import RPv_FIy_PublicDigest
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGl_DigestNumeric
open Aeneas Aeneas.Std FIq_Native
open FIw_ArrayValue (decoded)
def data : Array field.QM31 8#usize := ⟨[⟨⟨1282277666#u32,258398959#u32⟩,⟨1638378185#u32,1292406984#u32⟩⟩,⟨⟨930638361#u32,2036928920#u32⟩,⟨1752459948#u32,1712472443#u32⟩⟩,⟨⟨578553330#u32,61442562#u32⟩,⟨1289327729#u32,1004767429#u32⟩⟩,⟨⟨2077804317#u32,421783147#u32⟩,⟨1328134831#u32,1858657591#u32⟩⟩,⟨⟨1382301100#u32,953248300#u32⟩,⟨1163747066#u32,1538346132#u32⟩⟩,⟨⟨656719766#u32,1087082578#u32⟩,⟨1529595874#u32,1983419182#u32⟩⟩,⟨⟨713568212#u32,1984638603#u32⟩,⟨2094838112#u32,1158495503#u32⟩⟩,⟨⟨15624180#u32,1461329802#u32⟩,⟨1436206174#u32,2109677318#u32⟩⟩],by rfl⟩
theorem lane0 : FIy_PublicDigest.model JFu_PublicSemantic.value JGl_NumericData.openings
    JGl_NumericData.selectors ⟨0,by decide⟩ = decoded data ⟨0,by decide⟩ := by
  jgl_words
#print axioms lane0
theorem lane1 : FIy_PublicDigest.model JFu_PublicSemantic.value JGl_NumericData.openings
    JGl_NumericData.selectors ⟨1,by decide⟩ = decoded data ⟨1,by decide⟩ := by
  jgl_words
#print axioms lane1
theorem lane2 : FIy_PublicDigest.model JFu_PublicSemantic.value JGl_NumericData.openings
    JGl_NumericData.selectors ⟨2,by decide⟩ = decoded data ⟨2,by decide⟩ := by
  jgl_words
#print axioms lane2
theorem lane3 : FIy_PublicDigest.model JFu_PublicSemantic.value JGl_NumericData.openings
    JGl_NumericData.selectors ⟨3,by decide⟩ = decoded data ⟨3,by decide⟩ := by
  jgl_words
#print axioms lane3
theorem lane4 : FIy_PublicDigest.model JFu_PublicSemantic.value JGl_NumericData.openings
    JGl_NumericData.selectors ⟨4,by decide⟩ = decoded data ⟨4,by decide⟩ := by
  jgl_words
#print axioms lane4
theorem lane5 : FIy_PublicDigest.model JFu_PublicSemantic.value JGl_NumericData.openings
    JGl_NumericData.selectors ⟨5,by decide⟩ = decoded data ⟨5,by decide⟩ := by
  jgl_words
#print axioms lane5
theorem lane6 : FIy_PublicDigest.model JFu_PublicSemantic.value JGl_NumericData.openings
    JGl_NumericData.selectors ⟨6,by decide⟩ = decoded data ⟨6,by decide⟩ := by
  jgl_words
#print axioms lane6
theorem lane7 : FIy_PublicDigest.model JFu_PublicSemantic.value JGl_NumericData.openings
    JGl_NumericData.selectors ⟨7,by decide⟩ = decoded data ⟨7,by decide⟩ := by
  jgl_words
#print axioms lane7
theorem value : FIy_PublicDigest.model JFu_PublicSemantic.value JGl_NumericData.openings
    JGl_NumericData.selectors=decoded data := by
  funext i
  fin_cases i
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
#print axioms value
end AspisR1.JGl_DigestNumeric
end
