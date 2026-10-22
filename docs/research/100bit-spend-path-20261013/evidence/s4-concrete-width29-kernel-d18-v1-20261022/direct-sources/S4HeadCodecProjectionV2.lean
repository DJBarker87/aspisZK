import S4HeadCodecProjectionV1

set_option autoImplicit false

namespace AspisR1S4HeadCodecProjectionV2

open AspisR1FastDotsTailFieldProductRootV1
open AspisR1FastDotsLiteralHeadSumRootV1
open AspisR1.ExactBaseProjection

/-- Lift the exact same-array power meaning over the 29-slot powers vector to
all 26 C1 head terms.  The selected-cell witness is derived from Array access;
callers do not provide a separate membership premise for each term. -/
theorem c1_m31_head_term_fin26
    {a : Aeneas.Std.Array Aeneas.Std.U8 608#usize}
    (c1 : AspisR1S4C1M31SourceSliceV1.C1)
    (c2 : AspisR1S4C1M31SourceSliceV1.C2)
    (g : Aeneas.Std.Array Wide 29#usize) (slot : Fin 4)
    (gamma : TowerWide)
    (hbytes : a.val.map AspisR1.ExtractedRecordByteValue.rawByte =
      AspisR1.MixedLeafEncoding.encodeC1 c1 ++
        AspisR1.MixedLeafEncoding.encodeC2 c2)
    (hpower : ∀ j : Fin 29,
      wideDecoded (g.val[j.val]'(by scalar_tac)) = gamma ^ j.val) :
    ∀ term : Fin 26,
      headTermValue a g slot.val term.val =
        embed ((c1 slot).1 term) * gamma ^ term.val := by
  intro term
  have hterm29 : term.val < (29#usize).val := by
    have ht := term.isLt
    scalar_tac
  let j : Fin 29 := ⟨term.val, hterm29⟩
  have hp := hpower j
  have hpow : wideDecoded (g.val[term.val]'(by scalar_tac)) =
      gamma ^ term.val := by
    simpa [j] using hp
  have hget : g.val[term.val]? =
      some (g.val[term.val]'(by scalar_tac)) := by
    simp
  exact AspisR1S4HeadCodecProjectionV1.c1_m31_head_term
    c1 c2 g slot term gamma _ hbytes hget hpow

#print axioms c1_m31_head_term_fin26

end AspisR1S4HeadCodecProjectionV2
