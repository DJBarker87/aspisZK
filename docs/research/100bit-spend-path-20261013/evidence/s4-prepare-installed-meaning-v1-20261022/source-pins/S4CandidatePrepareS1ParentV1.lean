import AspisR1CurrentCaller.Types
import CurrentPreparedScratchReachability
import CallerStage2Carrier
import S4PreparedNewS1AdapterV1
import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1S4CandidatePrepareS1ParentV1
open AspisR1CurrentCaller
open AspisR1S4PreparedNewS1AdapterV1

abbrev VError := AspisR1CurrentCaller.verifier.Error
abbrev CError := AspisR1CurrentCaller.aspis_core.r0.Error
abbrev CodecError := AspisR1CurrentCaller.compact.CodecError
abbrev U8 := Std.U8
abbrev Usize := Std.Usize
abbrev Wide := AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact
abbrev View := AspisR1CurrentCaller.verifier.View
abbrev Verified (H : Type) := AspisR1CurrentCaller.r1_semantic.Verified H
abbrev Prepared := AspisR1CurrentCaller.verifier.Prepared

/- Explicit leaf slots from the emitted caller body.  This record does not
   assert semantics for these calls; their source owners remain separately bound. -/
structure Leaves (H : Type) where
  logicalSemantic : Result Usize
  logicalY1 : Result Usize
  offSemantic : Result Usize
  offY1 : Result Usize
  offInactive : Result Usize
  filled : Usize → U8 → Result (core.result.Result (alloc.vec.Vec U8) CError)
  mapAllocError : core.result.Result (alloc.vec.Vec U8) CError → Result (core.result.Result (alloc.vec.Vec U8) VError)
  expandSemantic : Slice U8 → Slice U8 → Result ((core.result.Result Unit CodecError) × Slice U8)
  expandValues : Slice U8 → Slice U8 → Result ((core.result.Result Unit CodecError) × Slice U8)
  codecFrom : core.convert.From VError CodecError
  wideView : Slice U8 → Slice U8 → Slice U8 → Result (core.result.Result View VError)
  verifyObserved : AspisR1CurrentCaller.aspis_core.digest.Digest32 H →
    AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public →
    Slice U8 → H → Option (AspisR1CurrentCaller.verifier.Phase → Result Unit) →
    Result (core.result.Result (Verified H) AspisR1CurrentCaller.r1_wire.Error)
  mapWireError : core.result.Result (Verified H) AspisR1CurrentCaller.r1_wire.Error →
    Result (core.result.Result (Verified H) VError)
  mark : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit) →
    AspisR1CurrentCaller.verifier.Phase → Result Unit

/- Exact emitted `verifier.candidate.prepare` control-flow body, with the
   Prepared.new leaf replaced by the accepted S1 body adapter. -/
def prepareWithS1New {H : Type} (B : AspisR1PublicPreparation.PreparedScratchModel.Boundaries)
    (ops : Leaves H) (d : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (public1 : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H)
    (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (g : Array Wide 29#usize) :
    Result ((core.result.Result Prepared VError) × Array Wide 29#usize) := do
  let i ← ops.logicalSemantic
  let i1 ← ops.logicalY1
  let i2 ← i + i1
  let r ← ops.filled i2 0#u8
  let r1 ← ops.mapAllocError r
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (s, deref_mut_back) ← lift (alloc.vec.Vec.deref_mut val)
    let ((semantic, y1), split_at_mut_back) ← core.slice.Slice.split_at_mut s i
    let i3 ← ops.offSemantic
    let i4 ← ops.offY1
    let s1 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) proof { start := i3, «end» := i4 }
    let (r2, semantic1) ← ops.expandSemantic s1 semantic
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let i5 ← ops.offInactive
      let s2 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) proof { start := i4, «end» := i5 }
      let (r3, y11) ← ops.expandValues s2 y1
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let s3 := split_at_mut_back (semantic1, y11)
        let val1 := deref_mut_back s3
        let s4 ← alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) val1 { «end» := i }
        let s5 ← alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8) val1 { start := i }
        let r4 ← ops.wideView proof s4 s5
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue v =>
          let r5 ← ops.verifyObserved d public1 v.semantic hash obs
          let r6 ← ops.mapWireError r5
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r6
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val2 =>
            let _ ← ops.mark obs AspisR1CurrentCaller.verifier.Phase.Semantic
            prepareByS1Body B d val2 v hash g
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r7 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              AspisR1CurrentCaller.verifier.Prepared (core.convert.FromSame VError) residual
            ok (r7, g)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r5 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            AspisR1CurrentCaller.verifier.Prepared (core.convert.FromSame VError) residual
          ok (r5, g)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r4 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          AspisR1CurrentCaller.verifier.Prepared ops.codecFrom residual
        ok (r4, g)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r3 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        AspisR1CurrentCaller.verifier.Prepared ops.codecFrom residual
      ok (r3, g)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      AspisR1CurrentCaller.verifier.Prepared (core.convert.FromSame VError) residual
    ok (r2, g)

def prepareSlot {H : Type} (B : AspisR1PublicPreparation.PreparedScratchModel.Boundaries)
    (ops : Leaves H) :
    AspisR1CurrentCaller.aspis_core.digest.Digest32 H →
    AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public →
    Slice U8 → H → Option (AspisR1CurrentCaller.verifier.Phase → Result Unit) →
    Array Wide 29#usize → Result ((core.result.Result Prepared VError) × Array Wide 29#usize) :=
  fun d public1 proof hash obs g => prepareWithS1New B ops d public1 proof hash obs g

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) : ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

/-- A successful source-shaped parent run reaches the exact S1-adapted
    Prepared.new child with the same returned state and scratch. -/
theorem prepareWithS1New_success_child {H : Type}
    (B : AspisR1PublicPreparation.PreparedScratchModel.Boundaries)
    (ops : Leaves H) (d : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (public1 : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H)
    (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (g : Array Wide 29#usize) (out : Prepared) (scratch : Array Wide 29#usize)
    (h : prepareWithS1New B ops d public1 proof hash obs g = .ok (.Ok out, scratch)) :
    ∃ (sem : Verified H) (v : View),
      prepareByS1Body B d sem v hash g = .ok (.Ok out, scratch) := by
  unfold prepareWithS1New at h
  obtain ⟨i, hi, h⟩ := bind_ok_inv h
  obtain ⟨i1, hi1, h⟩ := bind_ok_inv h
  obtain ⟨i2, hi2, h⟩ := bind_ok_inv h
  obtain ⟨r, hr, h⟩ := bind_ok_inv h
  obtain ⟨r1, hr1, h⟩ := bind_ok_inv h
  obtain ⟨cf, hcf, h⟩ := bind_ok_inv h
  cases cf with
  | Break residual =>
      cases r1 with
      | Ok x => simp [core.result.Result.Insts.CoreOpsTry.branch] at hcf
      | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry.branch] at hcf
          subst residual
          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from, bind_tc_ok] at h
  | Continue val =>
      obtain ⟨pair, hpairop, h⟩ := bind_ok_inv h
      rcases pair with ⟨s, deref_mut_back⟩
      obtain ⟨splitPair, hsplit, h⟩ := bind_ok_inv h
      rcases splitPair with ⟨⟨semantic, y1⟩, split_at_mut_back⟩
      obtain ⟨i3, hi3, h⟩ := bind_ok_inv h
      obtain ⟨i4, hi4, h⟩ := bind_ok_inv h
      obtain ⟨s1, hs1, h⟩ := bind_ok_inv h
      obtain ⟨expandPair, hexpand, h⟩ := bind_ok_inv h
      rcases expandPair with ⟨r2, semantic1⟩
      obtain ⟨cf1, hcf1, h⟩ := bind_ok_inv h
      cases cf1 with
      | Break residual =>
          cases r2 with
          | Ok x => simp [core.result.Result.Insts.CoreOpsTry.branch] at hcf1
          | Err e =>
              simp [core.result.Result.Insts.CoreOpsTry.branch] at hcf1
              subst residual
              cases hconv : ops.codecFrom.from e <;>
                simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  hconv, bind_tc_ok] at h
      | Continue _ =>
          obtain ⟨i5, hi5, h⟩ := bind_ok_inv h
          obtain ⟨s2, hs2, h⟩ := bind_ok_inv h
          obtain ⟨expandPair2, hexpand2, h⟩ := bind_ok_inv h
          rcases expandPair2 with ⟨r3, y11⟩
          obtain ⟨cf2, hcf2, h⟩ := bind_ok_inv h
          cases cf2 with
          | Break residual =>
              cases r3 with
              | Ok x => simp [core.result.Result.Insts.CoreOpsTry.branch] at hcf2
              | Err e =>
                  simp [core.result.Result.Insts.CoreOpsTry.branch] at hcf2
                  subst residual
                  cases hconv : ops.codecFrom.from e <;>
                    simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                      hconv, bind_tc_ok] at h
          | Continue _ =>
              obtain ⟨s4, hs4, h⟩ := bind_ok_inv h
              obtain ⟨s5, hs5, h⟩ := bind_ok_inv h
              obtain ⟨r4, hr4, h⟩ := bind_ok_inv h
              obtain ⟨cf3, hcf3, h⟩ := bind_ok_inv h
              cases cf3 with
              | Break residual =>
                  cases r4 with
                  | Ok x => simp [core.result.Result.Insts.CoreOpsTry.branch] at hcf3
                  | Err e =>
                      simp [core.result.Result.Insts.CoreOpsTry.branch] at hcf3
                      subst residual
                      simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                        core.convert.FromSame.from, bind_tc_ok] at h
              | Continue v =>
                  obtain ⟨r5, hr5, h⟩ := bind_ok_inv h
                  obtain ⟨r6, hr6, h⟩ := bind_ok_inv h
                  obtain ⟨cf4, hcf4, h⟩ := bind_ok_inv h
                  cases cf4 with
                  | Break residual =>
                      cases r6 with
                      | Ok x => simp [core.result.Result.Insts.CoreOpsTry.branch] at hcf4
                      | Err e =>
                          simp [core.result.Result.Insts.CoreOpsTry.branch] at hcf4
                          subst residual
                          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                            core.convert.FromSame.from, bind_tc_ok] at h
                  | Continue val2 =>
                      obtain ⟨_, hmark, hchild⟩ := bind_ok_inv h
                      exact ⟨val2, v, hchild⟩

theorem prepareWithS1New_success_powers {H : Type}
    (B : AspisR1PublicPreparation.PreparedScratchModel.Boundaries)
    (ops : Leaves H) (d : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (public1 : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H)
    (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (g : Array Wide 29#usize) (out : Prepared) (scratch : Array Wide 29#usize)
    (h : prepareWithS1New B ops d public1 proof hash obs g = .ok (.Ok out, scratch)) :
    ∃ (gamma : AspisR1PublicPreparation.aspis_core.field.WideExact)
      (powers : Array AspisR1PublicPreparation.aspis_core.field.WideExact 29#usize),
      out.gamma = AspisR1S4PreparedNewS1AdapterV1.wFromP gamma ∧
      B.powers 29#usize gamma = .ok powers ∧
      AspisR1S4PreparedNewS1AdapterV1.wArrayFromP powers = scratch := by
  obtain ⟨sem, v, hchild⟩ := prepareWithS1New_success_child B ops d public1 proof hash obs g out scratch h
  exact AspisR1S4PreparedNewS1AdapterV1.prepareByS1Body_success_powers B d sem v hash out g scratch hchild

#print axioms prepareWithS1New_success_child
#print axioms prepareWithS1New_success_powers

end AspisR1S4CandidatePrepareS1ParentV1
