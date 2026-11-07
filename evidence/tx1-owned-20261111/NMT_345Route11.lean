import NMT_345Route10
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result NMT_stage1_owned
/-- Second route equality occurs only after the first returns false. -/
def route11 {W : Type} (c : Calls) (s : Parent W) : Result Ret := do
 let accepted ← c.c1 core.cmp.PartialEqU8 s.data (Array.make 2#usize [3#u8,11#u8])
 if accepted then admitted c s else .ok (.Err .InvalidInstructionData)
theorem route11_call {W : Type} (c : Calls) (s : Parent W) :
 route11 c s = (c.c1 core.cmp.PartialEqU8 s.data (Array.make 2#usize [3#u8,11#u8]) >>=
 fun accepted => if accepted then admitted c s else .ok (.Err .InvalidInstructionData)) := rfl
#print axioms route11_call
end NMT_345
