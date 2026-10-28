import NCV_CastHelpers
import NCV_ArrayRun
set_option autoImplicit false
namespace NCV_SequenceStep
open Aeneas Aeneas.Std Result

theorem step (b : Slice U8) (s i : Usize) (a : Array U64 8#usize)
    (bytes : Array U8 8#usize) (cap : b.val.length ≤ 768)
    (fit : s.val+64 ≤ b.val.length) (index : i.val<8)
    (field : (b.val.drop (s.val+8*i.val)).take 8=bytes.val) :
    ∃ next : Usize, next.val=i.val+1 ∧
      NCV_CastRef.sequences_loop.body b s a i=
        ok (.cont (a.set i (core.num.U64.from_le_bytes bytes),next)) := by
  have sm : (8#usize*i : Result Usize) ⦃ x=>x.val=8*i.val ⦄ := by
    apply UScalar.mul_spec <;> scalar_tac
  obtain ⟨offset,mul,offval⟩:=WP.spec_imp_exists sm
  have sa : (s+offset : Result Usize) ⦃ x=>x.val=s.val+offset.val ⦄ := by
    apply UScalar.add_spec <;> scalar_tac
  obtain ⟨addr,add,addrval⟩:=WP.spec_imp_exists sa
  have read:=NCV_CastHelpers.word64 b addr bytes (by omega) (by simpa only [addrval,offval] using field)
  obtain ⟨next,advance,nextval⟩:=NCV_Loop.advance i (by omega)
  obtain ⟨out,write,outval⟩:=WP.spec_imp_exists
    (Array.update_spec a i (core.num.U64.from_le_bytes bytes) (by scalar_tac))
  subst out
  refine ⟨next,nextval,?_⟩
  have h : i<8#usize := by scalar_tac
  simp only [NCV_CastRef.sequences_loop.body,h,ite_true,mul,add,read,write,advance,bind_tc_ok]

theorem terminal (b : Slice U8) (s i : Usize) (a : Array U64 8#usize)
    (index : 8 ≤ i.val) : NCV_CastRef.sequences_loop.body b s a i=ok (.done a) := by
  have h : ¬i<8#usize := by scalar_tac
  simp only [NCV_CastRef.sequences_loop.body,h,ite_false]

#print axioms step
#print axioms terminal
end NCV_SequenceStep
