import NFB_RowPrimitives
set_option autoImplicit false
namespace NFB_RowLog
open Aeneas Aeneas.Std Result
abbrev Call := NFB_RowRef.NFB_RowCall
abbrev Log := NFB_RowRef.NFB_RowLog

def calls (c0 c1 c2 c3 : Call) : Array Call 4#usize := Array.make 4#usize [c0,c1,c2,c3]
def state (i : Usize) (c0 c1 c2 c3 : Call) : Log := ⟨calls c0 c1 c2 c3,i⟩
def event (kind : U8) (a b reply reply2 : U32) : Call := ⟨kind,a,b,reply,reply2⟩
def empty : Call := ⟨0#u8,0#u32,0#u32,0#u32,0#u32⟩
def initial : Log := state 0#usize empty empty empty empty

theorem step0 (c0 c1 c2 c3 : Call) (kind : U8) (a b r r2 : U32) :
 NFB_RowRef.NFB_row_call (state 0#usize c0 c1 c2 c3) kind a b r r2=
 ok (state 1#usize (event kind a b r r2) c1 c2 c3) := by
 simp [NFB_RowRef.NFB_row_call,state,calls,event,Array.update,Array.getElem?_Usize_eq,Array.make]
 all_goals scalar_tac

theorem step1 (c0 c1 c2 c3 : Call) (kind : U8) (a b r r2 : U32) :
 NFB_RowRef.NFB_row_call (state 1#usize c0 c1 c2 c3) kind a b r r2=
 ok (state 2#usize c0 (event kind a b r r2) c2 c3) := by
 simp [NFB_RowRef.NFB_row_call,state,calls,event,Array.update,Array.getElem?_Usize_eq,Array.make]
 all_goals scalar_tac

theorem step2 (c0 c1 c2 c3 : Call) (kind : U8) (a b r r2 : U32) :
 NFB_RowRef.NFB_row_call (state 2#usize c0 c1 c2 c3) kind a b r r2=
 ok (state 3#usize c0 c1 (event kind a b r r2) c3) := by
 simp [NFB_RowRef.NFB_row_call,state,calls,event,Array.update,Array.getElem?_Usize_eq,Array.make]
 all_goals scalar_tac

theorem step3 (c0 c1 c2 c3 : Call) (kind : U8) (a b r r2 : U32) :
 NFB_RowRef.NFB_row_call (state 3#usize c0 c1 c2 c3) kind a b r r2=
 ok (state 4#usize c0 c1 c2 (event kind a b r r2)) := by
 simp [NFB_RowRef.NFB_row_call,state,calls,event,Array.update,Array.getElem?_Usize_eq,Array.make]
 all_goals scalar_tac

#print axioms step0
#print axioms step1
#print axioms step2
#print axioms step3
end NFB_RowLog
