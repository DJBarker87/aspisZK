import S4LiteralN8PackingRootV1
import ExtractedCurrentReducer

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1FastDotsLiteralN8TotalV1

open AspisR1FastDotsLiteralN8PackingRootV1 (Ops Limbs Values literalEight readReduce)

def withReducer (base : Ops) : Ops :=
  {base with m31ReduceU64 := AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64}

theorem read_reduce_total (base : Ops) (limbs : Limbs) (i : Usize)
    (hi : i.val < 8) :
    ∃ value, readReduce (withReducer base) limbs i = .ok value := by
  obtain ⟨word, hread, _⟩ := WP.spec_imp_exists
    (Array.index_usize_spec limbs i (by simpa [Array.length, limbs.property] using hi))
  obtain ⟨value, hreduce, _hmod, _hcanonical⟩ :=
    AspisR1.ExtractedCurrentReducer.current_wrapper_mod word
  refine ⟨value, ?_⟩
  simp only [readReduce, hread, bind_tc_ok, withReducer, hreduce]

theorem literal_eight_total (base : Ops) (limbs : Limbs) :
    ∃ values : Values,
      literalEight (withReducer base) limbs = .ok values := by
  obtain ⟨m0, h0⟩ := read_reduce_total base limbs 0#usize (by decide)
  obtain ⟨m1, h1⟩ := read_reduce_total base limbs 1#usize (by decide)
  obtain ⟨m2, h2⟩ := read_reduce_total base limbs 2#usize (by decide)
  obtain ⟨m3, h3⟩ := read_reduce_total base limbs 3#usize (by decide)
  obtain ⟨m4, h4⟩ := read_reduce_total base limbs 4#usize (by decide)
  obtain ⟨m5, h5⟩ := read_reduce_total base limbs 5#usize (by decide)
  obtain ⟨m6, h6⟩ := read_reduce_total base limbs 6#usize (by decide)
  obtain ⟨m7, h7⟩ := read_reduce_total base limbs 7#usize (by decide)
  refine ⟨Array.make 8#usize [m0,m1,m2,m3,m4,m5,m6,m7], ?_⟩
  unfold literalEight
  simp only [h0,h1,h2,h3,h4,h5,h6,h7,bind_tc_ok]

/-- If the old P6 N8 call succeeds, its value is the value of the concrete
eight-read/reduce sequence; this uses totality plus the existing forward
same-output theorem, not an independent output equality premise. -/
theorem literal_eight_success_same_p6_output (base : Ops) (limbs : Limbs)
    (values : Values)
    (hp6 : AspisR1FromFnP6Generated.arrayFromFnP6 8#usize
      (AspisR1FastDotsLiteralN8PackingRootV1.InnerFn (withReducer base)) limbs = .ok values) :
    literalEight (withReducer base) limbs = .ok values := by
  obtain ⟨actual, hliteral⟩ := literal_eight_total base limbs
  have hp6' := AspisR1FastDotsLiteralN8PackingRootV1.literal_eight_success_p6_same_output
    (withReducer base) limbs actual hliteral
  have hvalue : actual=values := Result.ok.inj (hp6'.symm.trans hp6)
  simpa only [hvalue] using hliteral

#print axioms read_reduce_total
#print axioms literal_eight_total
#print axioms literal_eight_success_same_p6_output

end AspisR1FastDotsLiteralN8TotalV1
