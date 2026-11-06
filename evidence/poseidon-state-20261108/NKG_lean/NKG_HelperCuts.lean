import NKG_InternalSource
import NKG_FullSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_HelperCuts
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FJh_Base (State cell)
abbrev Seven := Array NQ 7#usize
abbrev Constants7 := Array U32 7#usize
abbrev Packed := Array NQ 4#usize
/-- Exact extensional transcription of K013/K011/K012. Full fields are
asserted by arbitrary coordinate, not by any child-result equation. -/
structure Internal (s l : State) (weights : Fin 2 → Seven) (constants : Fin 2 → Constants7)
 (dots : Fin 2 → NQ) (states replies : Fin 2 → State) (roundConstants : Fin 2 → NQ)
 (out : State) (dotCalls roundCalls : Nat) : Prop where
 dotCount : dotCalls=2
 roundCount : roundCalls=2
 weightArgs : ∀ c i,cell (weights c) i=cell l ⟨i.val+2,by have hi : i.val<7 := i.isLt;change i.val+2<16;omega⟩
 constantArgs : ∀ c i,cell (constants c) i=FJh_InternalConstants.value ⟨2*i.val+c.val,by have hi : i.val<7 := i.isLt;have hc : c.val<2 := c.isLt;omega⟩
 firstState : states 0=s
 secondState : states 1=replies 0
 scalarArgs : ∀ c,roundConstants c=dots c
 returned : out=replies 1
/-- K014/K015/K016; SAME three selected selectors, all six table rows and
full states/constants/return. No canonicality is added to the native cut. -/
structure Full (s l : State) (weights : Fin 2 → Array NQ 3#usize)
 (columns : Fin 2 → Fin 3 → Array U32 16#usize) (replies states constants : Fin 2 → State)
 (middle : State) (packed out : Packed) (columnCalls roundCalls : Nat) : Prop where
 columnCount : columnCalls=2
 roundCount : roundCalls=2
 weightArgs : ∀ c i,cell (weights c) i=cell l
   (if i.val=0 then ⟨1,by decide⟩ else if i.val=1 then ⟨9,by decide⟩ else ⟨10,by decide⟩)
 constantArgs : ∀ c i k,cell (columns c i) k=
   if i.val=0 then cell (FJb_InitialConstants.row ⟨2+c.val,by have := c.isLt;omega⟩) k
   else cell (FJe_FinalConstants.row ⟨2*(i.val-1)+c.val,by have hi : i.val<3 := i.isLt;have hc : c.val<2 := c.isLt;omega⟩) k
 firstState : states 0=s
 secondState : states 1=middle
 constantReplies : ∀ c,constants c=replies c
 returned : out=packed
#print Internal
#print Full
end AspisR1.NKG_HelperCuts
end
