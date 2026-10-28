import NDG_ZeroLoop
set_option autoImplicit false
namespace NDG_ZeroStep
open Aeneas Aeneas.Std Result

def byte (b : Slice U8) (i : Nat) : U8 := (b.val[i]?).getD 0#u8

theorem read (b : Slice U8) (i : Usize) (bound : i.val < b.val.length) :
    Slice.index_usize b i=ok (byte b i.val) := by
  obtain ⟨v,run,value⟩ := WP.spec_imp_exists
    (Slice.index_usize_spec b i (by simpa only [Slice.length] using bound))
  rw [value] at run
  simpa only [byte,List.getElem?_eq_getElem bound,Option.getD_some] using run

theorem terminal (b : Slice U8) (i : Usize) (bound : b.val.length ≤ i.val) :
    AdapterRw.r1_pool_adapter.owned.require_zero_loop.body b i=ok (.done none) := by
  have h : ¬i<Slice.len b := by scalar_tac
  simp only [AdapterRw.r1_pool_adapter.owned.require_zero_loop.body,h,ite_false]

theorem step (b : Slice U8) (i : Usize) (cap : b.val.length ≤ 65536)
    (bound : i.val < b.val.length) :
    ∃ next : Usize, next.val=i.val+1 ∧
      AdapterRw.r1_pool_adapter.owned.require_zero_loop.body b i=
        if byte b i.val ≠ 0#u8 then ok (.done (some (.Err AdapterRw.solana_program_error.ProgramError.AccountAlreadyInitialized))) else ok (.cont next) := by
  let next := Usize.wrapping_add i 1#usize
  have value : next.val = i.val+1 := NDG_ZeroLoop.wrapping_advance i (by omega)
  refine ⟨next,value,?_⟩
  have h : i<Slice.len b := by scalar_tac
  simp only [AdapterRw.r1_pool_adapter.owned.require_zero_loop.body,h,ite_true,
    read b i bound,bind_tc_ok]
  split <;> simp_all [next]

#print axioms read
#print axioms terminal
#print axioms step
end NDG_ZeroStep
