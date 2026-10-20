import AspisR1Stage2ResumeSuffix.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1Stage2ResumeSuffix

theorem successful_suffix_prepared_eq
    (bytes : Slice Std.U8) (v : transport.Variant)
    (roots : Array (Array Std.U8 32#usize) 2#usize)
    (gamma kappa : aspis_core.field.WideExact)
    (alpha : Array aspis_core.field.WideExact 2#usize)
    (rho : aspis_core.field.QM31)
    (queries : Array Std.U32 22#usize)
    (semantic_alpha : Array aspis_core.field.QM31 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize)
    (claim : aspis_core.field.WideExact) (state : Array Std.U8 32#usize)
    (weights : alloc.vec.Vec aspis_core.field.QM31)
    (rhs : aspis_core.field.WideExact) (power : aspis_core.field.QM31)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (h : verifier.resume_prepared_suffix bytes v roots gamma kappa alpha rho queries
      semantic_alpha z claim state weights rhs power = .ok (.Ok (p, a))) :
    p = { variant := v, roots := roots, gamma := gamma, kappa := kappa,
          alpha := alpha, rho := rho, queries := queries,
          semantic_alpha := semantic_alpha, z := z, claim := claim, state := state } := by
  unfold verifier.resume_prepared_suffix at h
  cases hindex : Slice.index_usize bytes 9#usize with
  | fail e => simp [hindex] at h
  | div => simp [hindex] at h
  | ok byte =>
    cases hcast : lift (UScalar.cast .Usize byte) with
    | fail e => simp [hindex, hcast] at h
    | div => simp [hindex, hcast] at h
    | ok next =>
      simp [hindex, hcast] at h
      exact h.1.symm

#print axioms successful_suffix_prepared_eq
end AspisR1Stage2ResumeSuffix
