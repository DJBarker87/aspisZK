import AspisR1DecodeKFullHelperCanonicality
import AspisR1DecodeKCanonicalArrayInvariant

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Aeneas Aeneas.Std Result WP
namespace AspisR1DecodeKFullLoopBodyPendingFrame

abbrev U8 := UScalar UScalarTy.U8
abbrev Range := core.ops.range.Range Usize

open AspisR1DecodeKCanonicalArrayInvariant

theorem loop_body_shape_preserves_canonical
    {n : Usize} (self : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (i : U8) (offset_values byte_offset : Usize) (iter : Range) (out : Array QM n)
    (value : Usize) (iter1 : Range) (cf : ControlFlow (Range × Array QM n)
      (Array QM n × Option (core.result.Result (Array QM n) DecodeError)))
    (hactive : iter.start.val < n.val) (hvalue : value.val < n.val)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some value, iter1)) (hout : CanonicalArray out)
    (hbody : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop.body
      self i offset_values byte_offset iter out = .ok cf) :
    (match cf with
      | .cont (iterOut, out1) => iterOut = iter1 ∧ ∃ q : QM, Canonical q ∧ out1 = out.set value q
      | .done (out1, pending) => out1 = out ∧ CanonicalArray out1 ∧
          ∃ e : DecodeError, pending = some (core.result.Result.Err e)) := by
  cases hcall : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_value
      { row := i, framed := self.framed } byte_offset value offset_values with
  | fail e =>
      simp [AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop.body,
        hnext, hcall] at hbody
  | div =>
      simp [AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop.body,
        hnext, hcall] at hbody
  | ok result =>
      cases result with
      | Err e =>
          have heval : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop.body
              self i offset_values byte_offset iter out =
              Aeneas.Std.Result.ok (.done (out, some (core.result.Result.Err e))) := by
            simp [AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop.body,
              hnext, hcall, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
          have hcf : cf = .done (out, some (.Err e)) :=
            Result.ok.inj (hbody.symm.trans heval)
          subst cf
          exact ⟨rfl, hout, e, rfl⟩
      | Ok q =>
          have hq : Canonical q :=
            AspisR1DecodeKFullHelperCanonicality.decode_k_value_success_canonical
              { row := i, framed := self.framed } byte_offset value offset_values q hcall
          cases hu : Array.update out value q with
          | fail e =>
              simp [AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop.body,
                hnext, hcall, core.result.Result.Insts.CoreOpsTry.branch, hu] at hbody
          | div =>
              simp [AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop.body,
                hnext, hcall, core.result.Result.Insts.CoreOpsTry.branch, hu] at hbody
          | ok outSpec =>
              obtain ⟨outExpected, hspec, hset⟩ := update_success_set out value q hvalue
              rw [hu] at hspec
              have houtSpec : outSpec = out.set value q := by
                have heq := Result.ok.inj hspec
                exact heq.trans hset
              have heval : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop.body
                  self i offset_values byte_offset iter out =
                  Aeneas.Std.Result.ok (.cont (iter1, outSpec)) := by
                simp [AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop.body,
                  hnext, hcall, core.result.Result.Insts.CoreOpsTry.branch, hu]
              have hcanonicalSpec : CanonicalArray outSpec := by
                rw [houtSpec]
                exact set_canonical_public out value q hout hq
              have hcf : cf = .cont (iter1, outSpec) :=
                Result.ok.inj (hbody.symm.trans heval)
              subst cf
              exact ⟨rfl, q, hq, houtSpec⟩

#print axioms loop_body_shape_preserves_canonical
end AspisR1DecodeKFullLoopBodyPendingFrame
