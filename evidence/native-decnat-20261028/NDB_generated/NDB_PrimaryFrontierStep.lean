import NDB_PrimaryEquality
import NCV_ArrayRun
set_option autoImplicit false
namespace NDB_PrimaryFrontierStep
open Aeneas Aeneas.Std Result
local instance : Inhabited (Array U32 8#usize) := ⟨Array.repeat 8#usize 0#u32⟩

theorem step (tree : Slice U8) (next : U64) (a : Array (Array U32 8#usize) 20#usize)
    (i : Usize) (row : Array U32 8#usize) (tag : U64) (index : i.val<20)
    (read : ∀ addr : Usize, addr.val=48+32*i.val → NCV_Reference.digest tree addr=ok (.Ok row))
    (shift : next >>> i=ok tag)
    (empty : tag &&& 1#u64=0#u64 → row=NCV_ArrayFrame.coord NCV_Reference.EMPTY i.val) :
    ∃ successor : Usize, successor.val=i.val+1 ∧
      NCV_Reference.decode_frontier_loop.body tree next a i=ok (.cont (a.set i row,successor)) := by
  have sm : (32#usize*i : Result Usize) ⦃ x=>x.val=32*i.val ⦄ := by
    apply UScalar.mul_spec <;> scalar_tac
  obtain ⟨offset,mul,offval⟩:=WP.spec_imp_exists sm
  have sa : (48#usize+offset : Result Usize) ⦃ x=>x.val=48+offset.val ⦄ := by
    apply UScalar.add_spec <;> scalar_tac
  obtain ⟨addr,add,addrval⟩:=WP.spec_imp_exists sa
  have digest:=read addr (by omega)
  have rd:=NCV_ArrayRead.read a i index
  have writeBackCall : Array.index_mut_usize a i=ok (NCV_ArrayFrame.coord a i.val,a.set i) := by
    unfold Array.index_mut_usize
    rw [rd]
    rfl
  have re:=NCV_ArrayRead.read NCV_Reference.EMPTY i (by scalar_tac)
  obtain ⟨successor,advance,value⟩:=NCV_Loop.advance i (by omega)
  refine ⟨successor,value,?_⟩
  have lt : i<20#usize := by scalar_tac
  simp only [NCV_Reference.decode_frontier_loop.body,lt,ite_true,mul,add,digest,
    core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,writeBackCall,shift,lift]
  by_cases bit : tag &&& 1#u64=0#u64
  · have eq : NCV_Reference.eq_digest row (NCV_ArrayFrame.coord NCV_Reference.EMPTY i.val)=ok true := by
      rw [empty bit]
      exact NDB_PrimaryEquality.digest_reflexive _
    simp only [bit,ite_true,re,eq,bind_tc_ok,advance] <;> rfl
  · simp only [bit,ite_false,advance,bind_tc_ok] <;> rfl

theorem terminal (tree : Slice U8) (next : U64) (a : Array (Array U32 8#usize) 20#usize)
    (i : Usize) (index : 20 ≤ i.val) :
    NCV_Reference.decode_frontier_loop.body tree next a i=ok (.done (.Ok a)) := by
  have no : ¬i<20#usize := by scalar_tac
  simp only [NCV_Reference.decode_frontier_loop.body,no,ite_false]

#print axioms step
#print axioms terminal
end NDB_PrimaryFrontierStep
