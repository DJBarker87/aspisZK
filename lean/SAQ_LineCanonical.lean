import SAQ_LineSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_LineCanonical
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide AspisR1CurrentWide.Proof SAQ_LineSource

theorem on_cuts (alpha a b c d out : E) (lx ly lz : U32)
    (cut : Cuts alpha a b c d lx ly lz out) : CanonicalWide out := by
  have first := scale cut.we2 cut.h0 quarter cut.Hh0
  have last := SAQ_RawWide.mul_exact alpha cut.we12 cut.we13 cut.Hwe13
  exact (wide_add_success cut.h0 cut.we13 out first.1 last.1 cut.Hout).1

theorem made (alpha a b c d out : E) (ix iy lx ly lz : U32)
    (h : line alpha (Array.make 4#usize [a,b,c,d])
      (Array.make 5#usize [ix,iy,lx,ly,lz])=ok out) : CanonicalWide out := by
  obtain ⟨cut⟩ := cuts alpha a b c d out ix iy lx ly lz h
  exact on_cuts alpha a b c d out lx ly lz cut

#print axioms on_cuts
#print axioms made
end AspisR1.SAQ_LineCanonical
end
