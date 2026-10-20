import AspisR1RhoTransactions.Funs
import CuSavingsRhoAllocationSuccess
import CuSavingsRhoResumeCaller
import CuSavingsRhoStage
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoTransactions
open Aeneas Aeneas.Std Result AspisR1RhoTransactions
open CuSavingsRhoInitRow CuSavingsRhoResumeLoans CuSavingsRhoEmptyReserveModel
variable [AspisR1RhoAccumulate.AccumulateCommon] [AspisR1RhoQuery.QueryCommon]

/-- Sufficient heap is numeric, evaluated at the transaction-local reservation.
8199 covers every admitted coefficient length (32*256 plus alignment slack).
The extra `future` budget is preserved for unchanged remaining allocations. -/
theorem stage_equivalence {H : Type} (digest : aspis_core.Digest32 H)
    (start len cursor : Usize) (future : Nat) (h64 : UScalarTy.Usize.numBits=64)
    (hfree : start.val+8+8199+future ≤ cursor.val)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array aspis_core.field.WideExact 29#usize) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : QueryGeometry) (end1 : Usize)
    (he : end1.val ≤ 22) (hr : Canonical p.rho) (hp : Canonical a.power)
    (hc : CuSavingsRhoResumeCaller.CanonicalWeights a.weights)
    (hl : (alloc.vec.Vec.len a.weights).val ≤ 256) :
    letI : AspisR1CuRho.HeapReserve := heapReserve (CuSavingsRhoAllocationSuccess.raw4Backend start len cursor)
    stage_new digest v p a g hash obs geometry end1 =
      stage_old digest v p a g hash obs geometry end1 := by
  letI : AspisR1CuRho.HeapReserve := heapReserve (CuSavingsRhoAllocationSuccess.raw4Backend start len cursor)
  have hlen : a.weights.val.length ≤ 256 := by
    simpa only [alloc.vec.Vec.len,Slice.len_val,Slice.length] using hl
  have hi := CuSavingsRhoAllocationSuccess.initializer_success start len cursor future
    (alloc.vec.Vec.deref a.weights) h64 hlen (by
      change start.val+8+32*a.weights.val.length+7+future ≤ cursor.val
      omega)
  have hs := CuSavingsRhoStage.source_outcome digest v p a g hash obs geometry end1 he hr hp hc hl
  change stage_new digest v p a g hash obs geometry end1 = _ at hs
  rw [hs]
  unfold AspisR1RhoStage.BatchedWeights.new
  rw [hi]
  rfl

variable [AspisR1RhoResumeCaller.ResumeCommon] [TxCommon]

theorem tx1_finish_equivalence {H : Type} (digest : aspis_core.Digest32 H)
    (start len cursor : Usize) (future : Nat) (h64 : UScalarTy.Usize.numBits=64)
    (hfree : start.val+8+8199+future ≤ cursor.val)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array aspis_core.field.WideExact 29#usize) (public1 proof : Slice U8) (k : Usize)
    (hash : H) (obs : Option (verifier.Phase → Result Unit))
    (he : k.val ≤ 22) (hr : Canonical p.rho) (hp : Canonical a.power)
    (hc : CuSavingsRhoResumeCaller.CanonicalWeights a.weights)
    (hl : (alloc.vec.Vec.len a.weights).val ≤ 256) :
    letI : AspisR1CuRho.HeapReserve := heapReserve (CuSavingsRhoAllocationSuccess.raw4Backend start len cursor)
    tx_new.tx1_finish digest v p a g public1 proof k hash obs =
      tx_old.tx1_finish digest v p a g public1 proof k hash obs := by
  letI : AspisR1CuRho.HeapReserve := heapReserve (CuSavingsRhoAllocationSuccess.raw4Backend start len cursor)
  have hs : ∀ geometry,stage_new digest v p a g hash obs geometry k =
      stage_old digest v p a g hash obs geometry k := fun geometry =>
    stage_equivalence digest start len cursor future h64 hfree v p a g hash obs geometry k he hr hp hc hl
  unfold tx_new.tx1_finish tx_old.tx1_finish
  simp only [hs]


theorem tx2_equivalence {H : Type} (digest : aspis_core.Digest32 H)
    (start len cursor : Usize) (future : Nat) (h64 : UScalarTy.Usize.numBits=64)
    (hfree : start.val+8+8199+future ≤ cursor.val)
    (public1 proof checkpoint1 : Slice U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) :
    letI : AspisR1CuRho.HeapReserve := heapReserve (CuSavingsRhoAllocationSuccess.raw4Backend start len cursor)
    tx_new.tx2 digest public1 proof checkpoint1 hash obs =
      tx_old.tx2 digest public1 proof checkpoint1 hash obs := by
  letI : AspisR1CuRho.HeapReserve := heapReserve (CuSavingsRhoAllocationSuccess.raw4Backend start len cursor)
  unfold tx_new.tx2 tx_old.tx2
  cases hparse : verifier.View.parse proof with
  | fail e => simp only [hparse,bind_tc_fail]
  | div => simp only [hparse,bind_tc_div]
  | ok parsed =>
    simp only [hparse,bind_tc_ok]
    cases parsed with
    | Err e => rfl
    | Ok v =>
      simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
      cases hmark : verifier.mark obs verifier.Phase.Parsed with
      | fail e => simp only [hmark,bind_tc_fail]
      | div => simp only [hmark,bind_tc_div]
      | ok unit =>
        simp only [hmark,bind_tc_ok]
        cases hresume : source_resume digest checkpoint1 proof public1 v.variant hash with
        | fail e => simp only [hresume,bind_tc_fail]
        | div => simp only [hresume,bind_tc_div]
        | ok resumed =>
          simp only [hresume,bind_tc_ok]
          cases resumed with
          | Err e => rfl
          | Ok pair =>
            rcases pair with ⟨p,a⟩
            have hi := CuSavingsRhoResumeCaller.source_inputs digest checkpoint1 proof public1 v.variant hash p a hresume
            obtain ⟨hr,hp,hc,hl⟩ := hi
            have hs : ∀ (g : Array aspis_core.field.WideExact 29#usize) geometry,
                stage_new digest v p a g hash obs geometry 22#usize =
                stage_old digest v p a g hash obs geometry 22#usize := fun g geometry =>
              stage_equivalence digest start len cursor future h64 hfree v p a g hash obs geometry
                22#usize (by scalar_tac) hr hp hc hl
            let tail (step : Array aspis_core.field.WideExact 29#usize → QueryGeometry →
                Result (core.result.Result verifier.Accumulator verifier.Error)) :
                Result (core.result.Result Unit verifier.Error) := do
              let g ← weights.powers 29#usize p.gamma
              verifier.mark obs verifier.Phase.CheckpointRead
              let r2 ← QueryGeometry.for_range p.queries a.next 22#usize
              let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
              match cf2 with
              | .Continue geometry =>
                let r3 ← step g geometry
                let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
                match cf3 with
                | .Continue out => finish_relation v p out obs
                | .Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    Unit (core.convert.FromSame verifier.Error) residual
              | .Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  Unit (core.convert.FromSame verifier.Error) residual
            have hfun : (fun g geometry => stage_new digest v p a g hash obs geometry 22#usize) =
                (fun g geometry => stage_old digest v p a g hash obs geometry 22#usize) := by
              funext g geometry
              exact hs g geometry
            exact congrArg tail hfun

#print axioms tx2_equivalence

theorem tx2_authenticated_equivalence {H : Type} (digest : aspis_core.Digest32 H)
    (start len cursor : Usize) (future : Nat) (h64 : UScalarTy.Usize.numBits=64)
    (hfree : start.val+8+8199+future ≤ cursor.val)
    (public1 proof checkpoint1 : Slice U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) :
    letI : AspisR1CuRho.HeapReserve := heapReserve (CuSavingsRhoAllocationSuccess.raw4Backend start len cursor)
    tx_new.tx2_authenticated digest public1 proof checkpoint1 hash obs =
      tx_old.tx2_authenticated digest public1 proof checkpoint1 hash obs := by
  letI : AspisR1CuRho.HeapReserve := heapReserve (CuSavingsRhoAllocationSuccess.raw4Backend start len cursor)
  unfold tx_new.tx2_authenticated tx_old.tx2_authenticated
  cases hparse : View.parse_shape proof with
  | fail e => simp only [hparse,bind_tc_fail]
  | div => simp only [hparse,bind_tc_div]
  | ok parsed =>
    simp only [hparse,bind_tc_ok]
    cases parsed with
    | Err e => rfl
    | Ok v =>
      simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
      cases hmark : verifier.mark obs verifier.Phase.Parsed with
      | fail e => simp only [hmark,bind_tc_fail]
      | div => simp only [hmark,bind_tc_div]
      | ok unit =>
        simp only [hmark,bind_tc_ok]
        cases hresume : source_resume digest checkpoint1 proof public1 v.variant hash with
        | fail e => simp only [hresume,bind_tc_fail]
        | div => simp only [hresume,bind_tc_div]
        | ok resumed =>
          simp only [hresume,bind_tc_ok]
          cases resumed with
          | Err e => rfl
          | Ok pair =>
            rcases pair with ⟨p,a⟩
            have hi := CuSavingsRhoResumeCaller.source_inputs digest checkpoint1 proof public1 v.variant hash p a hresume
            obtain ⟨hr,hp,hc,hl⟩ := hi
            have hs : ∀ (g : Array aspis_core.field.WideExact 29#usize) geometry,
                stage_new digest v p a g hash obs geometry 22#usize =
                stage_old digest v p a g hash obs geometry 22#usize := fun g geometry =>
              stage_equivalence digest start len cursor future h64 hfree v p a g hash obs geometry
                22#usize (by scalar_tac) hr hp hc hl
            let tail (step : Array aspis_core.field.WideExact 29#usize → QueryGeometry →
                Result (core.result.Result verifier.Accumulator verifier.Error)) :
                Result (core.result.Result Unit verifier.Error) := do
              let g ← weights.powers 29#usize p.gamma
              verifier.mark obs verifier.Phase.CheckpointRead
              let r2 ← QueryGeometry.for_range p.queries a.next 22#usize
              let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
              match cf2 with
              | .Continue geometry =>
                let r3 ← step g geometry
                let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
                match cf3 with
                | .Continue out => finish_relation v p out obs
                | .Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    Unit (core.convert.FromSame verifier.Error) residual
              | .Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  Unit (core.convert.FromSame verifier.Error) residual
            have hfun : (fun g geometry => stage_new digest v p a g hash obs geometry 22#usize) =
                (fun g geometry => stage_old digest v p a g hash obs geometry 22#usize) := by
              funext g geometry
              exact hs g geometry
            exact congrArg tail hfun

#print axioms tx2_authenticated_equivalence
#print axioms stage_equivalence
#print axioms tx1_finish_equivalence
end AspisR1.CuSavingsRhoTransactions
