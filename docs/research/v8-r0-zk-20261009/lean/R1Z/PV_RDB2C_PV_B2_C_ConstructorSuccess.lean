import R1Z.PV_RDB2C_PV_B2_C_ConstructorStage0
import R1Z.PV_RDB2C_PV_B2_C_ResultCongruence
set_option autoImplicit false
namespace PV_B2_C_ConstructorSuccess
open Aeneas Aeneas.Std Result PV_B2_C_ArrayTotal
open PV_B2_C_WeightsNative PV_B2_C_ConstructorRows PV_B2_C_ConstructorStages

def staged (variant : transport.Variant) (alpha : Array K 10#usize)
    (z : Array Point 2#usize) : Result (core.result.Result host_weights.Weights verifier.Error) := do
  let points ← host_weights.state_only_statement_points alpha
  let q ← Array.index_usize alpha 8#usize
  let q1 ← Array.index_usize alpha 9#usize
  let factors := Array.repeat 5#usize (Array.repeat 5#usize
    (Array.repeat 4#usize aspis_core.field.QM31.ZERO))
  stage0 variant points (Array.make 2#usize [q,q1]) z factors

/-- Only syntactic source cutting: every field call and restoration is unchanged. -/
theorem new_eq_staged (variant : transport.Variant) (alpha : Array K 10#usize)
    (z : Array Point 2#usize) : host_weights.Weights.new variant alpha z = staged variant alpha z := by
  unfold host_weights.Weights.new staged
  change (host_weights.state_only_statement_points alpha >>= _) = (host_weights.state_only_statement_points alpha >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro points _
  change (Array.index_usize alpha 8#usize >>= _) = (Array.index_usize alpha 8#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q _
  change (Array.index_usize alpha 9#usize >>= _) = (Array.index_usize alpha 9#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q1 _
  let extra : Array K 2#usize := Array.make 2#usize [q,q1]
  let a := Array.repeat 4#usize aspis_core.field.QM31.ZERO
  let a1 := Array.repeat 5#usize a
  let factors := Array.repeat 5#usize a1
  unfold stage0
  change (Array.index_usize points 0#usize >>= _) = (Array.index_usize points 0#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a2 _
  change (Array.index_usize a2 3#usize >>= _) = (Array.index_usize a2 3#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a3 _
  change (Array.index_usize a2 2#usize >>= _) = (Array.index_usize a2 2#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a3 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a3 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q2 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q3 _
  change (aspis_core.field.QM31.mul q2 q3 >>= _) = (aspis_core.field.QM31.mul q2 q3 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q4 _
  change (aspis_core.field.QM31.mul a3 q3 >>= _) = (aspis_core.field.QM31.mul a3 q3 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q5 _
  change (aspis_core.field.QM31.mul q2 b >>= _) = (aspis_core.field.QM31.mul q2 b >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q6 _
  change (aspis_core.field.QM31.mul a3 b >>= _) = (aspis_core.field.QM31.mul a3 b >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q7 _
  change (Array.index_mut_usize factors 0#usize >>= _) = (Array.index_mut_usize factors 0#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a4, index_mut_back⟩ _
  change (Array.update a4 0#usize (Array.make 4#usize [ q4, q5, q6, q7 ] : Array
      aspis_core.field.QM31 4#usize) >>= _) = (Array.update a4 0#usize (Array.make 4#usize [ q4, q5, q6, q7 ] : Array
      aspis_core.field.QM31 4#usize) >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a5 _
  change (Array.index_usize a2 1#usize >>= _) = (Array.index_usize a2 1#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a6 _
  change (Array.index_usize a2 0#usize >>= _) = (Array.index_usize a2 0#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b1 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a6 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a6 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q8 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b1 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b1 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q9 _
  change (aspis_core.field.QM31.mul q8 q9 >>= _) = (aspis_core.field.QM31.mul q8 q9 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q10 _
  change (aspis_core.field.QM31.mul a6 q9 >>= _) = (aspis_core.field.QM31.mul a6 q9 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q11 _
  change (aspis_core.field.QM31.mul q8 b1 >>= _) = (aspis_core.field.QM31.mul q8 b1 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q12 _
  change (aspis_core.field.QM31.mul a6 b1 >>= _) = (aspis_core.field.QM31.mul a6 b1 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q13 _
  let factors1 := index_mut_back a5
  change (Array.index_mut_usize factors1 0#usize >>= _) = (Array.index_mut_usize factors1 0#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a7, index_mut_back1⟩ _
  change (Array.update a7 1#usize (Array.make 4#usize [ q10, q11, q12, q13 ] : Array
      aspis_core.field.QM31 4#usize) >>= _) = (Array.update a7 1#usize (Array.make 4#usize [ q10, q11, q12, q13 ] : Array
      aspis_core.field.QM31 4#usize) >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a8 _
  change (Array.index_usize a2 5#usize >>= _) = (Array.index_usize a2 5#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a9 _
  change (Array.index_usize a2 4#usize >>= _) = (Array.index_usize a2 4#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b2 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a9 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a9 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q14 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b2 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b2 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q15 _
  change (aspis_core.field.QM31.mul q14 q15 >>= _) = (aspis_core.field.QM31.mul q14 q15 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q16 _
  change (aspis_core.field.QM31.mul a9 q15 >>= _) = (aspis_core.field.QM31.mul a9 q15 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q17 _
  change (aspis_core.field.QM31.mul q14 b2 >>= _) = (aspis_core.field.QM31.mul q14 b2 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q18 _
  change (aspis_core.field.QM31.mul a9 b2 >>= _) = (aspis_core.field.QM31.mul a9 b2 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q19 _
  let factors2 := index_mut_back1 a8
  change (Array.index_mut_usize factors2 0#usize >>= _) = (Array.index_mut_usize factors2 0#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a10, index_mut_back2⟩ _
  change (Array.update a10 2#usize (Array.make 4#usize [ q16, q17, q18, q19 ] : Array
      aspis_core.field.QM31 4#usize) >>= _) = (Array.update a10 2#usize (Array.make 4#usize [ q16, q17, q18, q19 ] : Array
      aspis_core.field.QM31 4#usize) >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a11 _
  change (Array.index_usize a2 9#usize >>= _) = (Array.index_usize a2 9#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a12 _
  change (Array.index_usize a2 8#usize >>= _) = (Array.index_usize a2 8#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b3 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a12 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a12 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q20 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b3 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b3 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q21 _
  change (aspis_core.field.QM31.mul q20 q21 >>= _) = (aspis_core.field.QM31.mul q20 q21 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q22 _
  change (aspis_core.field.QM31.mul a12 q21 >>= _) = (aspis_core.field.QM31.mul a12 q21 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q23 _
  change (aspis_core.field.QM31.mul q20 b3 >>= _) = (aspis_core.field.QM31.mul q20 b3 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q24 _
  change (aspis_core.field.QM31.mul a12 b3 >>= _) = (aspis_core.field.QM31.mul a12 b3 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q25 _
  let factors3 := index_mut_back2 a11
  change (Array.index_mut_usize factors3 0#usize >>= _) = (Array.index_mut_usize factors3 0#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a13, index_mut_back3⟩ _
  change (Array.update a13 3#usize (Array.make 4#usize [ q22, q23, q24, q25 ] : Array
      aspis_core.field.QM31 4#usize) >>= _) = (Array.update a13 3#usize (Array.make 4#usize [ q22, q23, q24, q25 ] : Array
      aspis_core.field.QM31 4#usize) >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a14 _
  change (Array.index_usize a2 7#usize >>= _) = (Array.index_usize a2 7#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a15 _
  change (Array.index_usize a2 6#usize >>= _) = (Array.index_usize a2 6#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b4 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a15 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a15 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q26 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b4 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b4 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q27 _
  change (aspis_core.field.QM31.mul q26 q27 >>= _) = (aspis_core.field.QM31.mul q26 q27 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q28 _
  change (aspis_core.field.QM31.mul a15 q27 >>= _) = (aspis_core.field.QM31.mul a15 q27 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q29 _
  change (aspis_core.field.QM31.mul q26 b4 >>= _) = (aspis_core.field.QM31.mul q26 b4 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q30 _
  change (aspis_core.field.QM31.mul a15 b4 >>= _) = (aspis_core.field.QM31.mul a15 b4 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q31 _
  let factors4 := index_mut_back3 a14
  change (Array.index_mut_usize factors4 0#usize >>= _) = (Array.index_mut_usize factors4 0#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a16, index_mut_back4⟩ _
  change (Array.update a16 4#usize (Array.make 4#usize [ q28, q29, q30, q31 ] : Array
      aspis_core.field.QM31 4#usize) >>= _) = (Array.update a16 4#usize (Array.make 4#usize [ q28, q29, q30, q31 ] : Array
      aspis_core.field.QM31 4#usize) >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a17 _
  unfold stage1
  change (Array.index_usize points 1#usize >>= _) = (Array.index_usize points 1#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a18 _
  change (Array.index_usize a18 3#usize >>= _) = (Array.index_usize a18 3#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a19 _
  change (Array.index_usize a18 2#usize >>= _) = (Array.index_usize a18 2#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b5 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a19 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a19 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q32 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b5 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b5 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q33 _
  change (aspis_core.field.QM31.mul q32 q33 >>= _) = (aspis_core.field.QM31.mul q32 q33 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q34 _
  change (aspis_core.field.QM31.mul a19 q33 >>= _) = (aspis_core.field.QM31.mul a19 q33 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q35 _
  change (aspis_core.field.QM31.mul q32 b5 >>= _) = (aspis_core.field.QM31.mul q32 b5 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q36 _
  change (aspis_core.field.QM31.mul a19 b5 >>= _) = (aspis_core.field.QM31.mul a19 b5 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q37 _
  let factors5 := index_mut_back4 a17
  change (Array.index_mut_usize factors5 1#usize >>= _) = (Array.index_mut_usize factors5 1#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a20, index_mut_back5⟩ _
  change (Array.update a20 0#usize (Array.make 4#usize [ q34, q35, q36, q37 ] : Array
      aspis_core.field.QM31 4#usize) >>= _) = (Array.update a20 0#usize (Array.make 4#usize [ q34, q35, q36, q37 ] : Array
      aspis_core.field.QM31 4#usize) >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a21 _
  change (Array.index_usize a18 1#usize >>= _) = (Array.index_usize a18 1#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a22 _
  change (Array.index_usize a18 0#usize >>= _) = (Array.index_usize a18 0#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b6 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a22 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a22 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q38 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b6 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b6 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q39 _
  change (aspis_core.field.QM31.mul q38 q39 >>= _) = (aspis_core.field.QM31.mul q38 q39 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q40 _
  change (aspis_core.field.QM31.mul a22 q39 >>= _) = (aspis_core.field.QM31.mul a22 q39 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q41 _
  change (aspis_core.field.QM31.mul q38 b6 >>= _) = (aspis_core.field.QM31.mul q38 b6 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q42 _
  change (aspis_core.field.QM31.mul a22 b6 >>= _) = (aspis_core.field.QM31.mul a22 b6 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q43 _
  let factors6 := index_mut_back5 a21
  change (Array.index_mut_usize factors6 1#usize >>= _) = (Array.index_mut_usize factors6 1#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a23, index_mut_back6⟩ _
  change (Array.update a23 1#usize (Array.make 4#usize [ q40, q41, q42, q43 ] : Array
      aspis_core.field.QM31 4#usize) >>= _) = (Array.update a23 1#usize (Array.make 4#usize [ q40, q41, q42, q43 ] : Array
      aspis_core.field.QM31 4#usize) >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a24 _
  change (Array.index_usize a18 5#usize >>= _) = (Array.index_usize a18 5#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a25 _
  change (Array.index_usize a18 4#usize >>= _) = (Array.index_usize a18 4#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b7 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a25 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a25 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q44 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b7 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b7 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q45 _
  change (aspis_core.field.QM31.mul q44 q45 >>= _) = (aspis_core.field.QM31.mul q44 q45 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q46 _
  change (aspis_core.field.QM31.mul a25 q45 >>= _) = (aspis_core.field.QM31.mul a25 q45 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q47 _
  change (aspis_core.field.QM31.mul q44 b7 >>= _) = (aspis_core.field.QM31.mul q44 b7 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q48 _
  change (aspis_core.field.QM31.mul a25 b7 >>= _) = (aspis_core.field.QM31.mul a25 b7 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q49 _
  let factors7 := index_mut_back6 a24
  change (Array.index_mut_usize factors7 1#usize >>= _) = (Array.index_mut_usize factors7 1#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a26, index_mut_back7⟩ _
  change (Array.update a26 2#usize (Array.make 4#usize [ q46, q47, q48, q49 ] : Array
      aspis_core.field.QM31 4#usize) >>= _) = (Array.update a26 2#usize (Array.make 4#usize [ q46, q47, q48, q49 ] : Array
      aspis_core.field.QM31 4#usize) >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a27 _
  change (Array.index_usize a18 9#usize >>= _) = (Array.index_usize a18 9#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a28 _
  change (Array.index_usize a18 8#usize >>= _) = (Array.index_usize a18 8#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b8 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a28 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a28 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q50 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b8 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b8 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q51 _
  change (aspis_core.field.QM31.mul q50 q51 >>= _) = (aspis_core.field.QM31.mul q50 q51 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q52 _
  change (aspis_core.field.QM31.mul a28 q51 >>= _) = (aspis_core.field.QM31.mul a28 q51 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q53 _
  change (aspis_core.field.QM31.mul q50 b8 >>= _) = (aspis_core.field.QM31.mul q50 b8 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q54 _
  change (aspis_core.field.QM31.mul a28 b8 >>= _) = (aspis_core.field.QM31.mul a28 b8 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q55 _
  let factors8 := index_mut_back7 a27
  change (Array.index_mut_usize factors8 1#usize >>= _) = (Array.index_mut_usize factors8 1#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a29, index_mut_back8⟩ _
  change (Array.update a29 3#usize (Array.make 4#usize [ q52, q53, q54, q55 ] : Array
      aspis_core.field.QM31 4#usize) >>= _) = (Array.update a29 3#usize (Array.make 4#usize [ q52, q53, q54, q55 ] : Array
      aspis_core.field.QM31 4#usize) >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a30 _
  change (Array.index_usize a18 7#usize >>= _) = (Array.index_usize a18 7#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a31 _
  change (Array.index_usize a18 6#usize >>= _) = (Array.index_usize a18 6#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b9 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a31 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a31 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q56 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b9 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b9 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q57 _
  change (aspis_core.field.QM31.mul q56 q57 >>= _) = (aspis_core.field.QM31.mul q56 q57 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q58 _
  change (aspis_core.field.QM31.mul a31 q57 >>= _) = (aspis_core.field.QM31.mul a31 q57 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q59 _
  change (aspis_core.field.QM31.mul q56 b9 >>= _) = (aspis_core.field.QM31.mul q56 b9 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q60 _
  change (aspis_core.field.QM31.mul a31 b9 >>= _) = (aspis_core.field.QM31.mul a31 b9 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q61 _
  let factors9 := index_mut_back8 a30
  change (Array.index_mut_usize factors9 1#usize >>= _) = (Array.index_mut_usize factors9 1#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a32, index_mut_back9⟩ _
  change (Array.update a32 4#usize (Array.make 4#usize [ q58, q59, q60, q61 ] : Array
      aspis_core.field.QM31 4#usize) >>= _) = (Array.update a32 4#usize (Array.make 4#usize [ q58, q59, q60, q61 ] : Array
      aspis_core.field.QM31 4#usize) >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a33 _
  unfold stage2
  change (Array.index_usize points 2#usize >>= _) = (Array.index_usize points 2#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a34 _
  change (Array.index_usize a34 3#usize >>= _) = (Array.index_usize a34 3#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a35 _
  change (Array.index_usize a34 2#usize >>= _) = (Array.index_usize a34 2#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b10 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a35 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a35 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q62 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b10 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b10 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q63 _
  change (aspis_core.field.QM31.mul q62 q63 >>= _) = (aspis_core.field.QM31.mul q62 q63 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q64 _
  change (aspis_core.field.QM31.mul a35 q63 >>= _) = (aspis_core.field.QM31.mul a35 q63 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q65 _
  change (aspis_core.field.QM31.mul q62 b10 >>= _) = (aspis_core.field.QM31.mul q62 b10 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q66 _
  change (aspis_core.field.QM31.mul a35 b10 >>= _) = (aspis_core.field.QM31.mul a35 b10 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q67 _
  let factors10 := index_mut_back9 a33
  change (Array.index_mut_usize factors10 2#usize >>= _) = (Array.index_mut_usize factors10 2#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a36, index_mut_back10⟩ _
  change (Array.update a36 0#usize (Array.make 4#usize [ q64, q65, q66, q67 ] : Array
      aspis_core.field.QM31 4#usize) >>= _) = (Array.update a36 0#usize (Array.make 4#usize [ q64, q65, q66, q67 ] : Array
      aspis_core.field.QM31 4#usize) >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a37 _
  change (Array.index_usize a34 1#usize >>= _) = (Array.index_usize a34 1#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a38 _
  change (Array.index_usize a34 0#usize >>= _) = (Array.index_usize a34 0#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b11 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q68 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q69 _
  change (aspis_core.field.QM31.mul q68 q69 >>= _) = (aspis_core.field.QM31.mul q68 q69 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q70 _
  change (aspis_core.field.QM31.mul a38 q69 >>= _) = (aspis_core.field.QM31.mul a38 q69 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q71 _
  change (aspis_core.field.QM31.mul q68 b11 >>= _) = (aspis_core.field.QM31.mul q68 b11 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q72 _
  change (aspis_core.field.QM31.mul a38 b11 >>= _) = (aspis_core.field.QM31.mul a38 b11 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q73 _
  let factors11 := index_mut_back10 a37
  change (Array.index_mut_usize factors11 2#usize >>= _) = (Array.index_mut_usize factors11 2#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a39, index_mut_back11⟩ _
  change (Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize) >>= _) = (Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize) >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a40 _
  change (Array.index_usize a34 5#usize >>= _) = (Array.index_usize a34 5#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a41 _
  change (Array.index_usize a34 4#usize >>= _) = (Array.index_usize a34 4#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b12 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q74 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q75 _
  change (aspis_core.field.QM31.mul q74 q75 >>= _) = (aspis_core.field.QM31.mul q74 q75 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q76 _
  change (aspis_core.field.QM31.mul a41 q75 >>= _) = (aspis_core.field.QM31.mul a41 q75 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q77 _
  change (aspis_core.field.QM31.mul q74 b12 >>= _) = (aspis_core.field.QM31.mul q74 b12 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q78 _
  change (aspis_core.field.QM31.mul a41 b12 >>= _) = (aspis_core.field.QM31.mul a41 b12 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q79 _
  let factors12 := index_mut_back11 a40
  change (Array.index_mut_usize factors12 2#usize >>= _) = (Array.index_mut_usize factors12 2#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a42, index_mut_back12⟩ _
  change (Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize) >>= _) = (Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize) >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a43 _
  change (Array.index_usize a34 9#usize >>= _) = (Array.index_usize a34 9#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a44 _
  change (Array.index_usize a34 8#usize >>= _) = (Array.index_usize a34 8#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b13 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q80 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q81 _
  change (aspis_core.field.QM31.mul q80 q81 >>= _) = (aspis_core.field.QM31.mul q80 q81 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q82 _
  change (aspis_core.field.QM31.mul a44 q81 >>= _) = (aspis_core.field.QM31.mul a44 q81 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q83 _
  change (aspis_core.field.QM31.mul q80 b13 >>= _) = (aspis_core.field.QM31.mul q80 b13 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q84 _
  change (aspis_core.field.QM31.mul a44 b13 >>= _) = (aspis_core.field.QM31.mul a44 b13 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q85 _
  let factors13 := index_mut_back12 a43
  change (Array.index_mut_usize factors13 2#usize >>= _) = (Array.index_mut_usize factors13 2#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a45, index_mut_back13⟩ _
  change (Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize) >>= _) = (Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize) >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a46 _
  change (Array.index_usize a34 7#usize >>= _) = (Array.index_usize a34 7#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a47 _
  change (Array.index_usize a34 6#usize >>= _) = (Array.index_usize a34 6#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b14 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q86 _
  change (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14 >>= _) = (aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q87 _
  change (aspis_core.field.QM31.mul q86 q87 >>= _) = (aspis_core.field.QM31.mul q86 q87 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q88 _
  change (aspis_core.field.QM31.mul a47 q87 >>= _) = (aspis_core.field.QM31.mul a47 q87 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q89 _
  change (aspis_core.field.QM31.mul q86 b14 >>= _) = (aspis_core.field.QM31.mul q86 b14 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q90 _
  change (aspis_core.field.QM31.mul a47 b14 >>= _) = (aspis_core.field.QM31.mul a47 b14 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q91 _
  let factors14 := index_mut_back13 a46
  change (Array.index_mut_usize factors14 2#usize >>= _) = (Array.index_mut_usize factors14 2#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a48, index_mut_back14⟩ _
  change (Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize) >>= _) = (Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize) >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a49 _
  unfold stage3
  change (Array.index_usize z 0#usize >>= _) = (Array.index_usize z 0#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro scp _
  change (aspis_core.field.QM31.mul scp.x scp.y >>= _) = (aspis_core.field.QM31.mul scp.x scp.y >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q92 _
  let factors15 := index_mut_back14 a49
  change (Array.index_mut_usize factors15 3#usize >>= _) = (Array.index_mut_usize factors15 3#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a50, index_mut_back15⟩ _
  change (Array.update a50 0#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, scp.y, scp.x, q92 ] :
      Array aspis_core.field.QM31 4#usize) >>= _) = (Array.update a50 0#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, scp.y, scp.x, q92 ] :
      Array aspis_core.field.QM31 4#usize) >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a51 _
  change (host_weights.double scp.x >>= _) = (host_weights.double scp.x >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro x _
  change (host_weights.double x >>= _) = (host_weights.double x >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro y _
  change (aspis_core.field.QM31.mul x y >>= _) = (aspis_core.field.QM31.mul x y >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q93 _
  let factors16 := index_mut_back15 a51
  change (Array.index_mut_usize factors16 3#usize >>= _) = (Array.index_mut_usize factors16 3#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a52, index_mut_back16⟩ _
  change (Array.update a52 1#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x, y, q93 ] : Array
      aspis_core.field.QM31 4#usize) >>= _) = (Array.update a52 1#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x, y, q93 ] : Array
      aspis_core.field.QM31 4#usize) >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a53 _
  change (host_weights.double y >>= _) = (host_weights.double y >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro x1 _
  change (host_weights.double x1 >>= _) = (host_weights.double x1 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro y1 _
  change (aspis_core.field.QM31.mul x1 y1 >>= _) = (aspis_core.field.QM31.mul x1 y1 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q94 _
  let factors17 := index_mut_back16 a53
  change (Array.index_mut_usize factors17 3#usize >>= _) = (Array.index_mut_usize factors17 3#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a54, index_mut_back17⟩ _
  change (Array.update a54 2#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x1, y1, q94 ] : Array
      aspis_core.field.QM31 4#usize) >>= _) = (Array.update a54 2#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x1, y1, q94 ] : Array
      aspis_core.field.QM31 4#usize) >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a55 _
  change (host_weights.double y1 >>= _) = (host_weights.double y1 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro x2 _
  change (host_weights.double x2 >>= _) = (host_weights.double x2 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro y2 _
  change (aspis_core.field.QM31.mul x2 y2 >>= _) = (aspis_core.field.QM31.mul x2 y2 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q95 _
  let factors18 := index_mut_back17 a55
  change (Array.index_mut_usize factors18 3#usize >>= _) = (Array.index_mut_usize factors18 3#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a56, index_mut_back18⟩ _
  change (Array.update a56 3#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x2, y2, q95 ] : Array
      aspis_core.field.QM31 4#usize) >>= _) = (Array.update a56 3#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x2, y2, q95 ] : Array
      aspis_core.field.QM31 4#usize) >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a57 _
  change (host_weights.double y2 >>= _) = (host_weights.double y2 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro x3 _
  change (host_weights.double x3 >>= _) = (host_weights.double x3 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro y3 _
  change (aspis_core.field.QM31.mul x3 y3 >>= _) = (aspis_core.field.QM31.mul x3 y3 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q96 _
  let factors19 := index_mut_back18 a57
  change (Array.index_mut_usize factors19 3#usize >>= _) = (Array.index_mut_usize factors19 3#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a58, index_mut_back19⟩ _
  change (Array.update a58 4#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x3, y3, q96 ] : Array
      aspis_core.field.QM31 4#usize) >>= _) = (Array.update a58 4#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x3, y3, q96 ] : Array
      aspis_core.field.QM31 4#usize) >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a59 _
  change (host_weights.double y3 >>= _) = (host_weights.double y3 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro unused0 _
  unfold stage4
  change (Array.index_usize z 1#usize >>= _) = (Array.index_usize z 1#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro scp1 _
  change (aspis_core.field.QM31.mul scp1.x scp1.y >>= _) = (aspis_core.field.QM31.mul scp1.x scp1.y >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q97 _
  let factors20 := index_mut_back19 a59
  change (Array.index_mut_usize factors20 4#usize >>= _) = (Array.index_mut_usize factors20 4#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a60, index_mut_back20⟩ _
  change (Array.update a60 0#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, scp1.y, scp1.x, q97 ] :
      Array aspis_core.field.QM31 4#usize) >>= _) = (Array.update a60 0#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, scp1.y, scp1.x, q97 ] :
      Array aspis_core.field.QM31 4#usize) >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a61 _
  change (host_weights.double scp1.x >>= _) = (host_weights.double scp1.x >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro x4 _
  change (host_weights.double x4 >>= _) = (host_weights.double x4 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro y4 _
  change (aspis_core.field.QM31.mul x4 y4 >>= _) = (aspis_core.field.QM31.mul x4 y4 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q98 _
  let factors21 := index_mut_back20 a61
  change (Array.index_mut_usize factors21 4#usize >>= _) = (Array.index_mut_usize factors21 4#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a62, index_mut_back21⟩ _
  change (Array.update a62 1#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x4, y4, q98 ] : Array
      aspis_core.field.QM31 4#usize) >>= _) = (Array.update a62 1#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x4, y4, q98 ] : Array
      aspis_core.field.QM31 4#usize) >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a63 _
  change (host_weights.double y4 >>= _) = (host_weights.double y4 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro x5 _
  change (host_weights.double x5 >>= _) = (host_weights.double x5 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro y5 _
  change (aspis_core.field.QM31.mul x5 y5 >>= _) = (aspis_core.field.QM31.mul x5 y5 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q99 _
  let factors22 := index_mut_back21 a63
  change (Array.index_mut_usize factors22 4#usize >>= _) = (Array.index_mut_usize factors22 4#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a64, index_mut_back22⟩ _
  change (Array.update a64 2#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x5, y5, q99 ] : Array
      aspis_core.field.QM31 4#usize) >>= _) = (Array.update a64 2#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x5, y5, q99 ] : Array
      aspis_core.field.QM31 4#usize) >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a65 _
  change (host_weights.double y5 >>= _) = (host_weights.double y5 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro x6 _
  change (host_weights.double x6 >>= _) = (host_weights.double x6 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro y6 _
  change (aspis_core.field.QM31.mul x6 y6 >>= _) = (aspis_core.field.QM31.mul x6 y6 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q100 _
  let factors23 := index_mut_back22 a65
  change (Array.index_mut_usize factors23 4#usize >>= _) = (Array.index_mut_usize factors23 4#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a66, index_mut_back23⟩ _
  change (Array.update a66 3#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x6, y6, q100 ] : Array
      aspis_core.field.QM31 4#usize) >>= _) = (Array.update a66 3#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x6, y6, q100 ] : Array
      aspis_core.field.QM31 4#usize) >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a67 _
  change (host_weights.double y6 >>= _) = (host_weights.double y6 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro x7 _
  change (host_weights.double x7 >>= _) = (host_weights.double x7 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro y7 _
  change (aspis_core.field.QM31.mul x7 y7 >>= _) = (aspis_core.field.QM31.mul x7 y7 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q101 _
  let factors24 := index_mut_back23 a67
  change (Array.index_mut_usize factors24 4#usize >>= _) = (Array.index_mut_usize factors24 4#usize >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a68, index_mut_back24⟩ _
  change (Array.update a68 4#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x7, y7, q101 ] : Array
      aspis_core.field.QM31 4#usize) >>= _) = (Array.update a68 4#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x7, y7, q101 ] : Array
      aspis_core.field.QM31 4#usize) >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a69 _
  change (host_weights.double y7 >>= _) = (host_weights.double y7 >>= _)
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro unused1 _
  let factors25 := index_mut_back24 a69
  rfl

theorem staged_total (variant : transport.Variant) (alpha : Array K 10#usize)
    (z : Array Point 2#usize) : RustOk (staged variant alpha z) := by
  unfold staged
  apply bind_rust _ _ (PV_B2_C_WeightsTotal.points alpha)
  intro points
  apply bind_rust _ _ (read _ _ (by decide))
  intro q
  apply bind_rust _ _ (read _ _ (by decide))
  intro q1
  exact stage0_total variant points (Array.make 2#usize [q,q1]) z _

/-- Complete Result success, arbitrary typed alpha/point carriers, with no
canonicality or success precondition. Native allocation equivalence is separate. -/
theorem new_total (variant : transport.Variant) (alpha : Array K 10#usize)
    (z : Array Point 2#usize) : RustOk (host_weights.Weights.new variant alpha z) := by
  rw [new_eq_staged]
  exact staged_total variant alpha z

#print axioms new_eq_staged
#print axioms staged_total
#print axioms new_total
end PV_B2_C_ConstructorSuccess
