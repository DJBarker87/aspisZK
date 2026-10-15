import ExtractedMaskQM31Exact

/-!
Injectivity of the exact-tower view on canonical current QM31 values. This is
only a representation result; it does not assert parser or Rust-call equality.
-/
set_option autoImplicit false

namespace AspisR1.ExtractedMaskQM31Equality

abbrev CurrentQM := AspisR1.ExtractedMaskQM31Exact.CurrentQM
abbrev CurrentCanonicalQM := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev QM31Exact := AspisR1.ExtractedMaskQM31Exact.QM31Exact

open AspisR1.ExtractedMaskQM31Exact

theorem decode_eq_iff
    (x y : CurrentQM)
    (hx : CurrentCanonicalQM x) (hy : CurrentCanonicalQM y) :
    decode x = decode y ↔ x = y := by
  constructor
  · intro h
    have h00 : (x.c0.a.val : AspisV8R15.ExactTowerBase.M31Exact) =
        (y.c0.a.val : AspisV8R15.ExactTowerBase.M31Exact) :=
      congrArg (fun q : QM31Exact => q.re.re) h
    have h01 : (x.c0.b.val : AspisV8R15.ExactTowerBase.M31Exact) =
        (y.c0.b.val : AspisV8R15.ExactTowerBase.M31Exact) :=
      congrArg (fun q : QM31Exact => q.re.im) h
    have h10 : (x.c1.a.val : AspisV8R15.ExactTowerBase.M31Exact) =
        (y.c1.a.val : AspisV8R15.ExactTowerBase.M31Exact) :=
      congrArg (fun q : QM31Exact => q.im.re) h
    have h11 : (x.c1.b.val : AspisV8R15.ExactTowerBase.M31Exact) =
        (y.c1.b.val : AspisV8R15.ExactTowerBase.M31Exact) :=
      congrArg (fun q : QM31Exact => q.im.im) h
    have n00 : x.c0.a.val = y.c0.a.val := by
      have hval := congrArg ZMod.val h00
      rw [ZMod.val_natCast_of_lt hx.1.1,
        ZMod.val_natCast_of_lt hy.1.1] at hval
      exact hval
    have n01 : x.c0.b.val = y.c0.b.val := by
      have hval := congrArg ZMod.val h01
      rw [ZMod.val_natCast_of_lt hx.1.2,
        ZMod.val_natCast_of_lt hy.1.2] at hval
      exact hval
    have n10 : x.c1.a.val = y.c1.a.val := by
      have hval := congrArg ZMod.val h10
      rw [ZMod.val_natCast_of_lt hx.2.1,
        ZMod.val_natCast_of_lt hy.2.1] at hval
      exact hval
    have n11 : x.c1.b.val = y.c1.b.val := by
      have hval := congrArg ZMod.val h11
      rw [ZMod.val_natCast_of_lt hx.2.2,
        ZMod.val_natCast_of_lt hy.2.2] at hval
      exact hval
    have e00 : x.c0.a = y.c0.a := Aeneas.Std.UScalar.val_eq_imp x.c0.a y.c0.a n00
    have e01 : x.c0.b = y.c0.b := Aeneas.Std.UScalar.val_eq_imp x.c0.b y.c0.b n01
    have e10 : x.c1.a = y.c1.a := Aeneas.Std.UScalar.val_eq_imp x.c1.a y.c1.a n10
    have e11 : x.c1.b = y.c1.b := Aeneas.Std.UScalar.val_eq_imp x.c1.b y.c1.b n11
    cases x with
    | mk x0 x1 =>
      cases x0 with
      | mk xa xb =>
        cases x1 with
        | mk xc xd =>
          cases y with
          | mk y0 y1 =>
            cases y0 with
            | mk ya yb =>
              cases y1 with
              | mk yc yd =>
                simp_all
  · intro h
    cases h
    rfl

#print axioms decode_eq_iff

end AspisR1.ExtractedMaskQM31Equality
