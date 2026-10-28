import NCV_ZeroStep
set_option autoImplicit false
namespace NCV_ByteStep
open Aeneas Aeneas.Std Result

theorem step (b : Slice U8) (s i : Usize) (a : Array U8 32#usize)
    (cap : b.val.length ≤ 768) (fit : s.val+32 ≤ b.val.length) (index : i.val<32) :
    ∃ next : Usize, next.val=i.val+1 ∧
      NCV_Reference.bytes32_loop.body b s a i =
        ok (.cont (a.set i (NCV_ZeroStep.byte b (s.val+i.val)),next)) := by
  have spec : (s+i : Result Usize) ⦃ x => x.val=s.val+i.val ⦄ := by
    apply UScalar.add_spec <;> scalar_tac
  obtain ⟨addr,call,value⟩ := WP.spec_imp_exists spec
  obtain ⟨next,advance,nextval⟩ := NCV_Loop.advance i (by omega)
  have rd : Slice.index_usize b addr=ok (NCV_ZeroStep.byte b (s.val+i.val)) := by
    simpa only [value] using NCV_ZeroStep.read b addr (by omega)
  have update := Array.update_spec a i (NCV_ZeroStep.byte b (s.val+i.val)) (by scalar_tac)
  obtain ⟨out,run,outval⟩ := WP.spec_imp_exists update
  subst out
  refine ⟨next,nextval,?_⟩
  have h : i<32#usize := by scalar_tac
  simp only [NCV_Reference.bytes32_loop.body,h,ite_true,call,rd,run,advance,bind_tc_ok]

theorem terminal (b : Slice U8) (s i : Usize) (a : Array U8 32#usize)
    (index : 32 ≤ i.val) : NCV_Reference.bytes32_loop.body b s a i=ok (.done a) := by
  have h : ¬i<32#usize := by scalar_tac
  simp only [NCV_Reference.bytes32_loop.body,h,ite_false]

#print axioms step
#print axioms terminal
end NCV_ByteStep
