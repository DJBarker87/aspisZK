import R1Z.PV_RDCD4_BytesSource
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD4_ParserWindows
open Aeneas Aeneas.Std Result PV_RDCD4_SliceRange194

theorem compose {T : Type} (xs : List T) (a b c d : Nat) (h : d ≤ b-a) :
    window (window xs a b) c d=window xs (a+c) (a+d) := by
  simp only [window,List.drop_take,List.drop_drop,List.take_take]
  congr 2 <;> omega

theorem component_window (xs : List U8) (base i : Nat)
    (hi : i+4 ≤ 8) (hx : base+8 ≤ xs.length) :
    PV_RDCD4_BytesSource.component (window xs base (base+8)) i (i+4)=
      PV_RDCD4_BytesSource.component xs (base+i) (base+(i+4)) := by
  have hl : (window xs base (base+8)).length=8 := by
    have h := length xs base (base+8) hx
    omega
  unfold PV_RDCD4_BytesSource.component
  rw [success (window xs base (base+8)) i (i+4) (by omega) (by omega),
    success xs (base+i) (base+(i+4)) (by omega) (by omega),bind_tc_ok,bind_tc_ok,
    compose xs base (base+8) i (i+4) (by omega)]

/-- Successful checked windows retain exactly the same backing bytes. -/
theorem no_write {T : Type} (xs : List T) (a b : Nat)
    (ha : a ≤ b) (hb : b ≤ xs.length) :
    (do let out ← index xs a b;ok (out,xs))=ok (window xs a b,xs) := by
  rw [success xs a b ha hb,bind_tc_ok]
#print axioms compose
#print axioms component_window
#print axioms no_write
end R1Z.PV_RDCD4_ParserWindows
