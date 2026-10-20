import CurrentClaimPartsUpdates
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentPreparedClaim.ClaimParts
open Concrete ClaimTrace

theorem chain_final_parts {D H : Type} {ops : ClaimDotOps D} {inst : aspis_core.Digest32 H}
    {sem : r1_semantic.Verified H} {y1 : Slice U8} {g : Array E 29#usize}
    {k parts : Array E 7#usize} {iter : ClaimTrace.Range} {out : E}
    (trace : Chain ops inst sem y1 g k iter parts out)
    (hend : iter.end.val=6) (hi : iter.start.val≤6) :
    ∃ final : Array E 7#usize, verifier.prepared_claim_sum k final=Result.ok out ∧
      (∀ j (hj : j.val<7), j.val≤ iter.start.val → cell final j hj=cell parts j hj) ∧
      (∀ point : Usize, point.val<6 → iter.start.val≤ point.val →
        ∃ (i : Usize) (value : E) (hi : i.val<7),
          (point+1#usize : Result Usize)=Result.ok i ∧
          verifier.prepared_claim_dot ops inst sem y1 g point=Result.ok (core.result.Result.Ok value) ∧
          cell final i hi=value) := by
  induction trace with
  | done r a x he hs =>
    refine ⟨a,hs,?_,?_⟩
    · intro j hj hjle; rfl
    · intro point hp hge; omega
  | @step r r' a a' x point i value hn hd hinc hw tail ih =>
    obtain ⟨hpoint,hactive,hstart,hend'⟩ := next_some_step r r' point hn
    have hpval : point.val=r.start.val := congrArg UScalar.val hpoint
    have hpoint6 : point.val<6 := by omega
    have hival : i.val=point.val+1 := add_one_success_val point i hpoint6 hinc
    have hib : i.val<7 := by omega
    have hend1 : r'.end.val=6 := by rw [hend']; exact hend
    have hi1 : r'.start.val≤6 := by omega
    obtain ⟨final,hsum,hprefix,hfuture⟩ := ih hend1 hi1
    refine ⟨final,hsum,?_,?_⟩
    · intro j hj hle
      rw [hprefix j hj (by omega), update_cells a a' i value hib hw j hj]
      rw [if_neg (by omega)]
    · intro p hp hge
      by_cases he : p.val=point.val
      · have hpEq : p=point := UScalar.eq_of_val_eq he
        subst p
        refine ⟨i,value,hib,hinc,hd,?_⟩
        rw [hprefix i hib (by omega),update_cells a a' i value hib hw i hib,if_pos rfl]
      · exact hfuture p hp (by omega)

#print axioms chain_final_parts
end AspisR1CurrentPreparedClaim.ClaimParts
