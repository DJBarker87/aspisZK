import R1Z.ProverCommitStreamSource
set_option autoImplicit false
noncomputable section
namespace R1Z.RealR2_SeedGuard
attribute [local instance] Classical.propDecidable
open Aeneas Aeneas.Std Result
open AspisR1ProverStreams

theorem allM_ne (xs ys : List U8) (len : xs.length = ys.length) :
    List.allM (fun (p : U8 × U8) => do
      let b ← core.cmp.PartialEqU8.ne p.1 p.2
      ok (decide (¬ b = true))) (List.zip xs ys) = ok (decide (xs = ys)) := by
  induction xs generalizing ys with
  | nil =>
    have h : ys = [] := by cases ys <;> simp_all
    subst ys
    rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp only [List.length_cons, List.length_nil] at len; omega
    | cons y ys =>
      have ht : xs.length = ys.length := by simpa only [List.length_cons, Nat.add_right_cancel_iff] using len
      simp only [List.zip_cons_cons, List.allM, core.cmp.PartialEqU8, liftFun2, lift,
        core.cmp.impls.PartialEqU8.ne, bind_tc_ok]
      by_cases h : x = y
      · subst y
        simpa using ih ys ht
      · simp [h]
        rfl

theorem array_eq {n : Usize} (xs ys : Array U8 n) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 xs ys =
      ok (decide (xs = ys)) := by
  unfold core.array.equality.PartialEqArray.eq
  have len : xs.val.length = ys.val.length := by rw [xs.property, ys.property]
  rw [if_pos len]
  change List.allM (fun (p : U8 × U8) => do
    let b ← core.cmp.PartialEqU8.ne p.1 p.2
    ok (decide (¬ b = true))) (List.zip xs.val ys.val) = _
  rw [allM_ne xs.val ys.val len]
  have he : (xs.val = ys.val) ↔ xs = ys := ⟨Subtype.ext, congrArg Subtype.val⟩
  simp only [he]

#print axioms allM_ne
#print axioms array_eq
end R1Z.RealR2_SeedGuard
