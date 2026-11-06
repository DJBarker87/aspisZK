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
   obtain ⟨b,d,v,exec,vb,db,viewEq,count⟩ := NJE_CountRows.total n.val a n 0#usize 0#usize c hn
     (by simp) (by simp) (by simpa [MultiproofConeCountPhysical.unread] using sorted)
     (by simpa [MultiproofConeCountPhysical.unread] using range) (by simp;omega) (by simp)
   simp only [UScalar.ofNatCore_val_eq,Nat.sub_zero] at db viewEq count
   have projection : rows n.val (NJA_CountDrop.keys a) n.val 0 0 c.val=
       ((countLevel n.val (cells (NJA_CountDrop.keys a) 0 n.val)).1,
        c.val+(countLevel n.val (cells (NJA_CountDrop.keys a) 0 n.val)).2) := by
     simpa [MultiproofConeCountPhysical.unread,cells] using rows_projection n.val (NJA_CountDrop.keys a) n.val 0 0 c.val (by omega) (by omega)
   rw [projection] at viewEq count
   dsimp only at viewEq count
   have domains := MultiproofConeCountPhysicalLevels.next_domain
     (cells (NJA_CountDrop.keys a) 0 n.val) sorted (by simpa [cells] using hn) range
   simp only [cells,List.length_map,List.length_range] at domains
   obtain ⟨out,outcome,value⟩ := ih (NJE_CountRange.successor start) b v d
     (by rw [NJE_CountRange.value start active];omega) (by omega)
     (by rw [viewEq];exact domains.1) (by rw [viewEq];exact domains.2.2) (by omega)
   refine ⟨out,?_,?_⟩
   · rw [multiproof.node_count_loop0,loop.eq_def]
     dsimp only
     simp only [multiproof.node_count_loop0.body,NJE_CountRange.active start active,bind_tc_ok,exec]
     simpa [multiproof.node_count_loop0,multiproof.node_count_loop0.body] using outcome
   · rw [value,viewEq,count,nodeCount]
     have len : (cells (NJA_CountDrop.keys a) 0 n.val).length=n.val := by simp [cells]
     rw [len]
     simp only [Nat.add_assoc]

#print total
#print axioms total
end NJE_CountLevels
