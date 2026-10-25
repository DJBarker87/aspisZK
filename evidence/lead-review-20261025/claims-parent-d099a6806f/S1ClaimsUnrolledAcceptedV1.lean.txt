import S1ClaimsUnrolledParentV1
import S1QueryArrayOperationsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS1ClaimsUnrolledAccepted
open AspisS1ClaimsUnrolledSource
abbrev Row := Array aspis_core.field.QM31 29#usize
abbrev Claims := Array Row 3#usize
private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (out : B)
    (h : (m >>= k) = ok out) : ∃ value, m = ok value ∧ k value = ok out := by
  cases m with
  | ok value => exact ⟨value,rfl,h⟩
  | fail error => cases h
  | div => cases h
private theorem overwrite_three (before : Claims) (r0 r1 r2 : Row) :
    ((before.set 0#usize r0).set 1#usize r1).set 2#usize r2 =
      (⟨[r0,r1,r2],by simp⟩ : Claims) := by
  apply Subtype.ext
  obtain ⟨a,b,c,shape⟩ := List.length_eq_three.mp before.property
  change (((before.val.set 0 r0).set 1 r1).set 2 r2) = [r0,r1,r2]
  rw [shape]
  rfl

/-- ACCEPTED-ONLY for the complete emitted parent with four explicit primitive
ports. Each decoder success is derived from the same parent success. This is
not a concrete native instance of the four ports, nor unsafe-init equivalence. -/
theorem accepted_rows (ports : PrimitivePorts) (prefix1 : r1_wire.Prefix) (out : Claims)
    (accepted : candidate_claims.claims ports prefix1 = ok (.Ok out)) :
    ∃ frame r0 r1 r2,
      Array.index_usize prefix1.records 25#usize = ok frame ∧
      ports.decode 29#usize {row:=25#u8,framed:=frame} 0#usize = ok (.Ok r0) ∧
      ports.decode 29#usize {row:=25#u8,framed:=frame} 29#usize = ok (.Ok r1) ∧
      ports.decode 29#usize {row:=25#u8,framed:=frame} 58#usize = ok (.Ok r2) ∧
      out = (⟨[r0,r1,r2],by simp⟩ : Claims) := by
  obtain ⟨frame,lookup,_,validated⟩ := AspisS1ClaimsSourceReads.record25_exact prefix1
  have h := accepted
  unfold candidate_claims.claims at h
  rw [validated,bind_tc_ok] at h
  simp only [Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
  obtain ⟨allocation,_,h⟩ := bind_success _ _ _ h
  obtain ⟨mapped,_,h⟩ := bind_success _ _ _ h
  cases mapped with
  | Err error =>
    simp [Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,
      Aeneas.Std.core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
  | Ok vector =>
    simp only [Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
    obtain ⟨slice,_,h⟩ := bind_success _ _ _ h
    obtain ⟨converted,_,h⟩ := bind_success _ _ _ h
    obtain ⟨mapped,_,h⟩ := bind_success _ _ _ h
    cases mapped with
    | Err error =>
      simp [Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,
        Aeneas.Std.core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
    | Ok before =>
      simp only [Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      obtain ⟨decoded0,call0,h⟩ := bind_success _ _ _ h
      cases decoded0 with
      | Err error =>
        simp [Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,
          Aeneas.Std.core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
      | Ok r0 =>
        simp only [Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        rw [AspisS1QueryArrayOperations.index_mut_total before 0#usize (by scalar_tac),bind_tc_ok] at h
        obtain ⟨decoded1,call1,h⟩ := bind_success _ _ _ h
        cases decoded1 with
        | Err error =>
          simp [Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,
            Aeneas.Std.core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
        | Ok r1 =>
          simp only [Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
          rw [AspisS1QueryArrayOperations.index_mut_total (before.set 0#usize r0) 1#usize (by scalar_tac),bind_tc_ok] at h
          obtain ⟨decoded2,call2,h⟩ := bind_success _ _ _ h
          cases decoded2 with
          | Err error =>
            simp [Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,
              Aeneas.Std.core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
          | Ok r2 =>
            simp only [Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
            rw [AspisS1QueryArrayOperations.update_total _ 2#usize r2 (by scalar_tac),bind_tc_ok] at h
            have same : ((before.set 0#usize r0).set 1#usize r1).set 2#usize r2 = out := by
              exact (Result.ok.inj h) |> Aeneas.Std.core.result.Result.Ok.inj
            exact ⟨frame,r0,r1,r2,lookup,call0,call1,call2,same.symm.trans (overwrite_three before r0 r1 r2)⟩

#print axioms accepted_rows
end AspisS1ClaimsUnrolledAccepted
