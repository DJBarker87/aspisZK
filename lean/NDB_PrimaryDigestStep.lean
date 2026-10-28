import NDB_PrimaryWindow
import NCV_ArrayRun
set_option autoImplicit false
namespace NDB_PrimaryDigestStep
open Aeneas Aeneas.Std Result

theorem step (b : Slice U8) (s i : Usize) (a : Array U32 8#usize)
    (bytes : Array U8 4#usize) (cap : b.val.length ≤ 768)
    (fit : s.val+32 ≤ b.val.length) (index : i.val<8)
    (field : (b.val.drop (s.val+4*i.val)).take 4=bytes.val)
    (canonical : (core.num.U32.from_le_bytes bytes).val<2147483647) :
    ∃ next : Usize, next.val=i.val+1 ∧
      NCV_Reference.digest_loop.body b s a i=
        ok (.cont (a.set i (core.num.U32.from_le_bytes bytes),next)) := by
  have sm : (4#usize*i : Result Usize) ⦃ x=>x.val=4*i.val ⦄ := by
    apply UScalar.mul_spec <;> scalar_tac
  obtain ⟨offset,mul,offval⟩:=WP.spec_imp_exists sm
  have sa : (s+offset : Result Usize) ⦃ x=>x.val=s.val+offset.val ⦄ := by
    apply UScalar.add_spec <;> scalar_tac
  obtain ⟨addr,add,addrval⟩:=WP.spec_imp_exists sa
  have read:=NDB_PrimaryWindow.word32 b addr bytes (by omega) (by simpa only [addrval,offval] using field)
  obtain ⟨next,advance,nextval⟩:=NCV_Loop.advance i (by omega)
  obtain ⟨out,write,outval⟩:=WP.spec_imp_exists
    (Array.update_spec a i (core.num.U32.from_le_bytes bytes) (by scalar_tac))
  subst out
  refine ⟨next,nextval,?_⟩
  have h : i<8#usize := by scalar_tac
  have no : ¬core.num.U32.from_le_bytes bytes>=2147483647#u32 := by scalar_tac
  simp only [NCV_Reference.digest_loop.body,h,ite_true,mul,add,read,no,ite_false,write,advance,bind_tc_ok]

theorem terminal (b : Slice U8) (s i : Usize) (a : Array U32 8#usize)
    (index : 8 ≤ i.val) : NCV_Reference.digest_loop.body b s a i=ok (.done (a,none)) := by
  have h : ¬i<8#usize := by scalar_tac
  simp only [NCV_Reference.digest_loop.body,h,ite_false]

#print axioms step
#print axioms terminal
end NDB_PrimaryDigestStep
