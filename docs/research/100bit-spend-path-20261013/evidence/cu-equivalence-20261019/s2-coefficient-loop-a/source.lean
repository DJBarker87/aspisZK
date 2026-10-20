import CuSavingsS2SourceCoefficientStep
set_option autoImplicit false
namespace AspisR1.CuSavingsS2SourceCoefficientLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1S2Groups
open CuSavingsS2SourceArrays CuSavingsS2SourceCatalog
open OccupancyRangeTraversal
variable [Shared]

def execute {S V A : Type} (body : S → Result (ControlFlow S V)) (k : V → Result A) (state : S) : Result A := do
  let value ← loop body state
  k value

theorem execute_unroll {S V A : Type} (body : S → Result (ControlFlow S V)) (k : V → Result A) (state : S) :
    execute body k state = (do
      let flow ← body state
      match flow with | .done value => k value | .cont next => execute body k next) := by
  unfold execute
  rw [loop]
  cases h : body state with
  | fail e => rfl
  | div => rfl
  | ok flow => cases flow <;> rfl

def newStep (f : Slice U8) : Range × NewCoeffs → Result (ControlFlow (Range × NewCoeffs) NewCoeffs)
  | (iter,coeff) => new.s2_grouped_inactive_pair_loop0.body f iter coeff

def oldStep (w : Weights) (f : Slice U8) : Range × Masks × OldCoeffs × Usize →
    Result (ControlFlow (Range × Masks × OldCoeffs × Usize) (Masks × OldCoeffs × Usize))
  | (iter,masks,coeff,groups) => old.grouped_inactive_pair_loop0.body w f iter masks coeff groups

theorem cast_group (g : U8) : (UScalar.cast .Usize g).val=g.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  have hb : g.val<2^8 := g.bv.isLt
  have hbits : 32≤System.Platform.numBits := System.Platform.le_numBits
  have hs : (2:Nat)^8 ≤ 2^UScalarTy.Usize.numBits := by
    simp only [UScalarTy.numBits]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem source_transport {A : Type} (fuel : Nat) (w : Weights) (f : Slice U8)
    (iter : Range) (masks : Masks) (old : OldCoeffs) (new : NewCoeffs) (groups : Usize)
    (hw : w.variant=transport.Variant.S2) (he : iter.end.val=64) (hi : iter.start.val≤64)
    (hf : 64-iter.start.val=fuel) (hc : Catalog iter.start.val masks groups) (hv : CoeffEq old new)
    (kNew : NewCoeffs → Result A) (kOld : Masks → OldCoeffs → Usize → Result A)
    (hk : ∀ masks old new groups, Catalog 64 masks groups → CoeffEq old new → kNew new = kOld masks old groups) :
    (do let result ← new.s2_grouped_inactive_pair_loop0 iter f new;kNew result) =
    (do let (ms,coeff,n) ← old.grouped_inactive_pair_loop0 iter w f masks old groups;kOld ms coeff n) := by
  change execute (newStep f) kNew (iter,new) =
    execute (oldStep w f) (fun (ms,coeff,n) => kOld ms coeff n) (iter,masks,old,groups)
  induction fuel generalizing iter masks old new groups with
  | zero =>
    have hn := next_done iter (by omega)
    have hstart : iter.start.val=64 := by omega
    have hnew : newStep f (iter,new) = .ok (.done new) := by
      simp [newStep,new.s2_grouped_inactive_pair_loop0.body,hn]
    have hold : oldStep w f (iter,masks,old,groups) = .ok (.done (masks,old,groups)) := by
      simp [oldStep,old.grouped_inactive_pair_loop0.body,hn]
    rw [execute_unroll,execute_unroll,hnew,hold]
    exact hk masks old new groups (by simpa only [hstart] using hc) hv
  | succ fuel ih =>
    have hpos : iter.start.val<64 := by omega
    obtain ⟨next,hn,hinc,hend,_⟩ := next_step iter (by omega)
    obtain ⟨g8,hg8,hg8v,hg8b⟩ := CuSavingsS2SourceTables.group_source iter.start hpos
    let group := UScalar.cast .Usize g8
    have hgval : group.val=g8.val := cast_group g8
    have hgb : group.val<12 := by omega
    have hg : group.val=CuSavingsS2Tables.groupValue ⟨iter.start.val,hpos⟩ := hgval.trans hg8v
    obtain ⟨mask,hm,hmv⟩ := CuSavingsS2SourceTables.mask_source group hgb
    have hmask := CuSavingsS2SourceMask.source_mask w iter.start mask hw hpos
      (by rw [hmv,hg])
    have hsearch := search_from_catalog iter.start.val hpos masks groups group mask hc hg hgb hmv
    obtain ⟨masks1,groups1,hext,hcatalog⟩ := extend_success iter.start.val hpos masks groups group mask hc hg hgb hmv
    have hold := CuSavingsS2SourceCoefficientStep.old_body w f iter next masks masks1 old groups group groups1 mask
      hgb hn hmask hsearch hext
    have hnew := CuSavingsS2SourceCoefficientStep.new_body f iter next new g8 group hgb hn hg8 rfl
    rw [hv group.val hgb] at hold
    have hold' : oldStep w f (iter,masks,old,groups) = (do
        let value ← CuSavingsS2SourceCoefficientStep.term f iter.start (lookup new zero group.val)
        .ok (.cont (next,masks1,old.set group value,groups1))) := hold
    have hnew' : newStep f (iter,new) = (do
        let value ← CuSavingsS2SourceCoefficientStep.term f iter.start (lookup new zero group.val)
        .ok (.cont (next,new.set group value))) := hnew
    rw [execute_unroll,execute_unroll,hold',hnew']
    simp only [bind_assoc_eq,bind_tc_ok]
    apply (bind_eq_iff _ _ _).mpr
    intro value hvalue
    exact ih next masks1 (old.set group value) (new.set group value) groups1
      (by rw [hend];exact he) (by omega) (by omega)
      (by rw [hinc];exact hcatalog) (coeff_update old new group hgb hv value)

#print axioms execute_unroll
#print axioms cast_group
#print axioms source_transport
end AspisR1.CuSavingsS2SourceCoefficientLoop
