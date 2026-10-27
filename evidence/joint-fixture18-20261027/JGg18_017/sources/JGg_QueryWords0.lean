import JGg_Opening31
import Query31ConcreteWordsDriverChain
set_option autoImplicit false
namespace AspisR1.JGg_QueryWords0
open Aeneas Aeneas.Std Result
 def value : Array U32 8#usize := Array.make 8#usize [93499#u32,147529#u32,216823#u32,245899#u32,209371#u32,192317#u32,65593#u32,183859#u32]
theorem source : Query31ConcreteWordsDriverChain.actualQueryWords
    (AspisV8R19.SqueezeOracleBridge.encodeState JGg_Opening31.block0)=ok value := by
  rfl
#print axioms source
end AspisR1.JGg_QueryWords0
