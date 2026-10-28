import NDB_PrimaryFrontierStep
import NDB_DigestDecision
import NDB_RejectInduction
set_option autoImplicit false
namespace NDB_FrontierReject
open Aeneas Aeneas.Std Result
abbrev Row := Array U32 8#usize
abbrev Frontier := Array Row 20#usize
local instance : Inhabited Row := ⟨Array.repeat 8#usize 0#u32⟩

theorem digest_error (tree : Slice U8) (next : U64) (a : Frontier) (i : Usize)
    (index : i.val<20)
    (read : ∀ addr : Usize, addr.val=48+32*i.val → NCV_Reference.digest tree addr=ok (.Err ())) :
    NCV_Reference.decode_frontier_loop.body tree next a i=ok (.done (.Err ())) := by
  have sm : (32#usize*i : Result Usize) ⦃ x=>x.val=32*i.val ⦄ := by
    apply UScalar.mul_spec <;> scalar_tac
  obtain ⟨offset,mul,offval⟩:=WP.spec_imp_exists sm
  have sa : (48#usize+offset : Result Usize) ⦃ x=>x.val=48+offset.val ⦄ := by
    apply UScalar.add_spec <;> scalar_tac
  obtain ⟨addr,add,addrval⟩:=WP.spec_imp_exists sa
  have digest:=read addr (by omega)
  have lt : i<20#usize := by scalar_tac
  simp only [NCV_Reference.decode_frontier_loop.body,lt,ite_true,mul,add,digest,
    core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rfl

theorem vacant_error (tree : Slice U8) (next : U64) (a : Frontier) (i : Usize)
    (row : Row) (tag : U64) (index : i.val<20)
    (read : ∀ addr : Usize, addr.val=48+32*i.val → NCV_Reference.digest tree addr=ok (.Ok row))
    (shift : next >>> i=ok tag) (bit : tag &&& 1#u64=0#u64)
    (different : row≠NCV_ArrayFrame.coord NCV_Reference.EMPTY i.val) :
    NCV_Reference.decode_frontier_loop.body tree next a i=ok (.done (.Err ())) := by
  have sm : (32#usize*i : Result Usize) ⦃ x=>x.val=32*i.val ⦄ := by
    apply UScalar.mul_spec <;> scalar_tac
  obtain ⟨offset,mul,offval⟩:=WP.spec_imp_exists sm
  have sa : (48#usize+offset : Result Usize) ⦃ x=>x.val=48+offset.val ⦄ := by
    apply UScalar.add_spec <;> scalar_tac
  obtain ⟨addr,add,addrval⟩:=WP.spec_imp_exists sa
  have digest:=read addr (by omega)
  have rd:=NCV_ArrayRead.read a i index
  have back : Array.index_mut_usize a i=ok (NCV_ArrayFrame.coord a i.val,a.set i) := by
    unfold Array.index_mut_usize
    rw [rd]
    rfl
  have re:=NCV_ArrayRead.read NCV_Reference.EMPTY i (by scalar_tac)
  have eq:=NDB_DigestDecision.value row (NCV_ArrayFrame.coord NCV_Reference.EMPTY i.val)
  simp only [different,decide_false] at eq
  have lt : i<20#usize := by scalar_tac
  simp only [NCV_Reference.decode_frontier_loop.body,lt,ite_true,mul,add,digest,
    core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,back,shift,lift,bit,re,eq,
    Bool.false_eq_true,ite_false]
  rfl

theorem rejected (tree : Slice U8) (next : U64) (bad : Nat) (bound : bad<20)
    (target : Frontier)
    (fields : ∀ i : Usize, i.val<bad → ∀ addr : Usize, addr.val=48+32*i.val →
      NCV_Reference.digest tree addr=ok (.Ok (NCV_ArrayFrame.coord target i.val)))
    (guards : ∀ i : Usize, i.val<bad → ∃ tag : U64, next >>> i=ok tag ∧
      (tag &&& 1#u64=0#u64 → NCV_ArrayFrame.coord target i.val=NCV_ArrayFrame.coord NCV_Reference.EMPTY i.val))
    (failure : ∀ a : Frontier, ∀ i : Usize, i.val=bad →
      NCV_Reference.decode_frontier_loop.body tree next a i=ok (.done (.Err ()))) :
    NCV_Reference.decode_frontier tree next=ok (.Err ()) := by
  have steps : ∀ a (i : Usize), i.val<bad → ∃ successor : Usize,
      successor.val=i.val+1 ∧ NCV_Reference.decode_frontier_loop.body tree next a i=
        ok (.cont (a.set i (NCV_ArrayFrame.coord target i.val),successor)) := by
    intro a i hi
    obtain ⟨tag,shift,empty⟩:=guards i hi
    exact NDB_PrimaryFrontierStep.step tree next a i _ tag (by omega) (fields i hi) shift empty
  unfold NCV_Reference.decode_frontier NCV_Reference.decode_frontier_loop
  dsimp only
  exact NDB_RejectInduction.run _ (NCV_ArrayFrame.coord target) bad (core.result.Result.Err () : core.result.Result Frontier Unit) steps failure _ 0#usize (by scalar_tac)
#print axioms digest_error
#print axioms vacant_error
#print axioms rejected
end NDB_FrontierReject
