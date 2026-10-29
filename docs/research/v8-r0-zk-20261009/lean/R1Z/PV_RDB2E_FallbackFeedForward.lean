import R1Z.PV_RDB2E_FallbackStateCodec
import R1Z.PV_RDB2E_FallbackArray4

section
-- Unchanged source component R1Z.PV_CBL_FallbackFeedForward
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackFeedForward
open PV_CBL_FallbackScalar PV_CBL_FallbackArray4
set_option autoImplicit false
/-- Exact extracted feed-forward tail; saved i is the unmodified original state[0]. -/
def source (state : Array U32 8#usize) (abef cdgh : Array U32 4#usize) : Result (Array U32 8#usize) := do
  let i ← Array.index_usize state 0#usize
  let a17 ← Array.index_usize abef 0#usize
  let b ← Array.index_usize abef 1#usize
  let e ← Array.index_usize abef 2#usize
  let f ← Array.index_usize abef 3#usize
  let c ← Array.index_usize cdgh 0#usize
  let d ← Array.index_usize cdgh 1#usize
  let g ← Array.index_usize cdgh 2#usize
  let h ← Array.index_usize cdgh 3#usize
  let i24 ← lift (core.num.U32.wrapping_add i a17)
  let state1 ← Array.update state 0#usize i24
  let i25 ← Array.index_usize state1 1#usize
  let i26 ← lift (core.num.U32.wrapping_add i25 b)
  let state2 ← Array.update state1 1#usize i26
  let i27 ← Array.index_usize state2 2#usize
  let i28 ← lift (core.num.U32.wrapping_add i27 c)
  let state3 ← Array.update state2 2#usize i28
  let i29 ← Array.index_usize state3 3#usize
  let i30 ← lift (core.num.U32.wrapping_add i29 d)
  let state4 ← Array.update state3 3#usize i30
  let i31 ← Array.index_usize state4 4#usize
  let i32 ← lift (core.num.U32.wrapping_add i31 e)
  let state5 ← Array.update state4 4#usize i32
  let i33 ← Array.index_usize state5 5#usize
  let i34 ← lift (core.num.U32.wrapping_add i33 f)
  let state6 ← Array.update state5 5#usize i34
  let i35 ← Array.index_usize state6 6#usize
  let i36 ← lift (core.num.U32.wrapping_add i35 g)
  let state7 ← Array.update state6 6#usize i36
  let i37 ← Array.index_usize state7 7#usize
  let i38 ← lift (core.num.U32.wrapping_add i37 h)
  Array.update state7 7#usize i38

def value (s r : State) : State :=
  ⟨U32.wrapping_add s.a r.a,U32.wrapping_add s.b r.b,
   U32.wrapping_add s.c r.c,U32.wrapping_add s.d r.d,
   U32.wrapping_add s.e r.e,U32.wrapping_add s.f r.f,
   U32.wrapping_add s.g r.g,U32.wrapping_add s.h r.h⟩
theorem shape (s r : State) :
    source (PV_CBL_FallbackStateCodec.encode s) (pack r.a r.b r.e r.f) (pack r.c r.d r.g r.h) =
      ok (PV_CBL_FallbackStateCodec.encode (value s r)) := by
  simp [source,PV_CBL_FallbackStateCodec.encode,PV_CBL_FallbackArray8.pack,pack,value,
    Array.index_usize,Array.getElem?_Usize_eq,Array.update,Array.set,lift,bind_tc_ok]
  rfl
#print axioms source
#print axioms value
#print axioms shape
end R1Z.PV_CBL_FallbackFeedForward

end
