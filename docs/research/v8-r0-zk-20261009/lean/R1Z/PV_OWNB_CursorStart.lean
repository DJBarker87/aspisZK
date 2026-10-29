import R1Z.PV_OWNB_Cursor
set_option autoImplicit false
namespace R1Z.PV_OWNB_CursorStart
open PV_OWNB_Cursor PV_OWN_Heap PV_OWNB_LinkCodec
/-- Entry acquires one scope over the original allocation, retaining its generation. -/
def start (m : Memory) (t : Token) (owner : Nat) (c : Cell) (len cap : Nat)
 (values : Nat → PV_OWN_Link.Link) : Cursor :=
 ⟨m,t,owner,c,0,0,len,cap,values,values⟩

theorem valid (m : Memory) (t : Token) (owner : Nat) (c : Cell) (len cap : Nat)
 (values : Nat → PV_OWN_Link.Link) (h:Writable m owner t c)
 (size:c.size=cap*8) (align:c.alignment=2) (bound:len≤cap)
 (initialized:∀ i, i<len → NativeView c (i*8) (values i)) :
 PV_OWNB_Cursor.Valid (start m t owner c len cap values) := by
 unfold PV_OWNB_Cursor.Valid start
 dsimp only
 refine ⟨h,size,align,by omega,by omega,bound,?_,?_⟩
 · intro i _ hi; exact initialized i hi
 · intro i hi; change i<0 at hi; omega
#print axioms valid
end R1Z.PV_OWNB_CursorStart
