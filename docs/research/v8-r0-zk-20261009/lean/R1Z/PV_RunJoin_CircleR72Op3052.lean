import R1Z.PV_RunJoin_CircleR72Op2952
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op30 (left : Q) (right : Q) :
    AspisR72Sampler.field.r24_canonical_mul (encQ left) (encQ right) = (do let x ← PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul left right; ok ((Option.map encQ) x)) := by
  unfold AspisR72Sampler.field.r24_canonical_mul PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul
  simp only [q_c0,q_c1,cm_a,cm_b,op3]
  by_cases h0 : left.1.1 ≥ PV_RunJoin_CircleR72Raw52.field.P
  · rw [if_pos h0]
    all_goals rfl
  · rw [if_neg h0]
    by_cases h1 : left.1.2 ≥ PV_RunJoin_CircleR72Raw52.field.P
    · rw [if_pos h1]
      all_goals rfl
    · rw [if_neg h1]
      by_cases h2 : left.2.1 ≥ PV_RunJoin_CircleR72Raw52.field.P
      · rw [if_pos h2]
        all_goals rfl
      · rw [if_neg h2]
        by_cases h3 : left.2.2 ≥ PV_RunJoin_CircleR72Raw52.field.P
        · rw [if_pos h3]
          all_goals rfl
        · rw [if_neg h3]
          by_cases h4 : right.1.1 ≥ PV_RunJoin_CircleR72Raw52.field.P
          · rw [if_pos h4]
            all_goals rfl
          · rw [if_neg h4]
            by_cases h5 : right.1.2 ≥ PV_RunJoin_CircleR72Raw52.field.P
            · rw [if_pos h5]
              all_goals rfl
            · rw [if_neg h5]
              by_cases h6 : right.2.1 ≥ PV_RunJoin_CircleR72Raw52.field.P
              · rw [if_pos h6]
                all_goals rfl
              · rw [if_neg h6]
                by_cases h7 : right.2.2 ≥ PV_RunJoin_CircleR72Raw52.field.P
                · rw [if_pos h7]
                  all_goals rfl
                · rw [if_neg h7]
                  repeat' (first
                    | rw [op27]
                    | rw [op28]
                    | rw [op29]
                    | rw [bind_assoc_eq]
                    | rw [bind_tc_ok]
                    | (apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro value reachable))
                  all_goals simp only [Option.map_none,Option.map_some,encQ,encCM]
                  all_goals rfl

#print axioms op30
end R1Z.PV_RunJoin_CircleR72Ops52
