import NCO_Word
import NCO_ParserRef.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NCO_WordStep

theorem step (payload : Slice U8) (i j p q at1 a1 a2 a3 next : Usize)
    (a b c d : U8) (hj : j.val < 8)
    (m0 : 32#usize * i = ok p) (m1 : 4#usize * j = ok q)
    (addr : p + q = ok at1)
    (add1 : at1 + 1#usize = ok a1) (add2 : at1 + 2#usize = ok a2)
    (add3 : at1 + 3#usize = ok a3) (increment : j + 1#usize = ok next)
    (r0 : Slice.index_usize payload at1 = ok a)
    (r1 : Slice.index_usize payload a1 = ok b)
    (r2 : Slice.index_usize payload a2 = ok c)
    (r3 : Slice.index_usize payload a3 = ok d) :
    NCO_ParserRef.validate_ref_loop0_loop0.body payload i j =
      if NCO_Word.packed a b c d >= 2147483647#u32 then ok (.done (i,0#u32))
      else if j >= 4#usize then
        if NCO_Word.packed a b c d != 0#u32 then ok (.done (i,0#u32))
        else ok (.cont next)
      else ok (.cont next) := by
  have h : j < 8#usize := by scalar_tac
  simp only [NCO_ParserRef.validate_ref_loop0_loop0.body, h, ite_true,
    m0, m1, addr, add1, add2, add3, increment, r0, r1, r2, r3, lift, bind_tc_ok]
  rfl

#print axioms step
end NCO_WordStep
