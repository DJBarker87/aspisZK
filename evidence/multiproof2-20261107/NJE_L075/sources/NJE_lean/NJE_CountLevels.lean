import NJE_CountRange

set_option autoImplicit false
namespace NJE_CountLevels
open Aeneas Aeneas.Std Result ControlFlow NJA_Multiproof
open AspisR1 MultiproofConeCountPhysical MultiproofConeLiveOrder OraclePortFrozenOrder
attribute [local instance] Classical.propDecidable

theorem total (height : Nat) (start : U32) (a : Array U32 16#usize) (n c : Usize)
    (clock : start.val+height=18) (hn : n.val≤16)
    (sorted : (cells (NJA_CountDrop.keys a) 0 n.val).Pairwise (·<·))
    (range : ∀ x∈cells (NJA_CountDrop.keys a) 0 n.val, x<262144)
    (budget : c.val+16*height≤576) :
    ∃ d : Usize,
      multiproof.node_count_loop0 {start:=start,«end»:=18#u32} .Two a n c=ok d ∧
      d.val=c.val+nodeCount height (cells (NJA_CountDrop.keys a) 0 n.val) := by
 induction height generalizing start a n c with
 | zero =>
   have start_eq : start=18#u32 := by apply UScalar.eq_of_val_eq;simpa using clock
   subst start
   refine ⟨c,?_,by simp [nodeCount]⟩
   rw [multiproof.node_count_loop0,loop.eq_def]
   simp [multiproof.node_count_loop0.body,NJE_CountRange.exit]
 | succ height ih =>
   have active : start.val<18 := by omega
   have unread : unread (NJA_CountDrop.keys a) n.val 0=cells (NJA_CountDrop.keys a) 0 n.val := by
     simp [MultiproofConeCountPhysical.unread]
   obtain ⟨b,d,v,exec,vb,db,prefix,count⟩ := NJE_CountRows.total n.val a n 0#usize 0#usize c hn
     (by simp) (by simp) (by simpa only [unread] using sorted)
     (by simpa only [unread] using range) (by simp;omega) (by simp)
   have level := level_projection (NJA_CountDrop.keys a) n.val
   have projection : rows n.val (NJA_CountDrop.keys a) n.val 0 0 c.val=
       ((countLevel n.val (cells (NJA_CountDrop.keys a) 0 n.val)).1,
        c.val+(countLevel n.val (cells (NJA_CountDrop.keys a) 0 n.val)).2) := by
     simpa [unread] using rows_projection n.val (NJA_CountDrop.keys a) n.val 0 0 c.val sorted
   rw [projection] at prefix count
   have domains := MultiproofConeCountPhysicalLevels.next_domain
     (cells (NJA_CountDrop.keys a) 0 n.val) sorted (by simpa [cells] using hn) range
   obtain ⟨out,outcome,value⟩ := ih (NJE_CountRange.successor start) b v d
     (by rw [NJE_CountRange.value start active];omega) (by omega)
     (by rw [prefix];exact domains.1) (by rw [prefix];exact domains.2.2) (by omega)
   refine ⟨out,?_,?_⟩
   · rw [multiproof.node_count_loop0,loop.eq_def]
     dsimp only
     simp only [multiproof.node_count_loop0.body,NJE_CountRange.active start active,bind_tc_ok,exec]
     simpa only [multiproof.node_count_loop0] using outcome
   · rw [value,prefix,count,nodeCount]
     have len : (cells (NJA_CountDrop.keys a) 0 n.val).length=n.val := by simp [cells]
     rw [len]
     omega

#print total
#print axioms total
end NJE_CountLevels
