import R1Z.PV_RunJoin_PartsCells19
import R0Z.PoseidonCanon
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CopyCertificate20
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_RunJoin_BankCertificate19 PV_Src_PortSboxStep
abbrev M := PV_RunJoin_FixtureRecords.M

def model (c : Certificate) : R0Z.BuilderModel.BlockIn M := ⟨liftA c.pre,liftA c.absorption⟩

theorem permutation (c : Certificate)
    (hc : ∀ n, n < 11 → Canonical (c.states (n+1)))
    (hm : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model c) (n+1) = liftA (c.states (n+1))) :
    ∃ rounds, R0PoseidonCopy.perm_rounds c.pre c.absorption = ok rounds ∧
      ∀ n, n < 11 → rounds.val[n]! = c.states (n+1) := by
  obtain ⟨rounds,hr,hv⟩ := perm_rounds_lift c.pre c.absorption (model c) ⟨fun _ => rfl,fun _ => rfl⟩
  refine ⟨rounds,hr,?_⟩
  intro n hn
  apply PV_RunJoin_NullifierPermutation17.state_injective _ _
    (fun j => perm_canon _ _ _ hr n hn j.val j.isLt) (hc n hn)
  funext j
  exact (hv n j hn).trans (congrFun (hm n hn) j)
#print axioms permutation

theorem writer (c : Certificate)
    (hc : ∀ n, n < 11 → Canonical (c.states (n+1)))
    (hm : ∀ n, n < 11 → R0Z.BuilderModel.blockIter (model c) (n+1) = liftA (c.states (n+1))) :
    ∃ block, (do let rounds ← R0PoseidonCopy.perm_rounds c.pre c.absorption
                 R0BlockCopies.write_block c.pre c.absorption rounds) = ok block ∧
      ∀ row, row < 16 → ∀ lane, lane < 16 →
        block.val[row*16+lane]! = (c.row row).val[lane]! := by
  obtain ⟨rounds,hr,hv⟩ := permutation c hc hm
  obtain ⟨block,hb,hcell⟩ := block_spec c.pre c.absorption rounds
  refine ⟨block,by rw [hr];simp only [bind_tc_ok];exact hb,?_⟩
  intro row hrow lane hlane
  rw [hcell]
  unfold BlockVal Certificate.row
  by_cases hz : row = 0
  · subst row
    simp only [Nat.zero_mul,Nat.zero_add,if_true,if_pos hlane]
  · rw [if_neg hz,if_neg (by omega)]
    by_cases hr12 : row < 12
    · rw [if_pos hr12,if_pos (by omega)]
      have hd : (row*16+lane)/16-1 = row-1 := by omega
      have hl : (row*16+lane)%16 = lane := by omega
      rw [hd,hl,hv (row-1) (by omega),show row-1+1=row by omega]
    · rw [if_neg hr12,if_neg (by omega)]
      by_cases he : row = 12
      · subst row
        rw [if_pos rfl,if_pos (by omega),show 12*16+lane-192=lane by omega]
      · rw [if_neg he,if_neg (by omega)]
        rw [Array.repeat_val]
        simp only [List.getElem!_eq_getElem?_getD,List.getElem?_replicate,
          show lane < (16#usize : Usize).val by simpa using hlane,if_true,Option.getD_some]
        with_unfolding_all rfl
#print axioms writer
end R1Z.PV_RunJoin_CopyCertificate20
