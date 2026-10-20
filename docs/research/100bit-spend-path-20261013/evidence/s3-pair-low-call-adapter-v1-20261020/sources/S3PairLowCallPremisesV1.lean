import S3PairLowCallReadFactsV1

open Aeneas Aeneas.Std Result WP
set_option autoImplicit false

namespace AspisR1PairLowCallCut

open AspisR1S3PowersLowEntryCanonicalV1

/-- The successful generated permutation and array reads carry the actual
bounds needed to interpret both four-element inputs. This is derived from the
read theorem, not assumed by the callback consumer. -/
theorem actual_pair_callback_read_bounds
    (c : weights.s2_twofold_low_array.closure)
    (i : Std.Usize) (hi : i.val < 16) :
    ∃ r d p q x y,
      UScalar.rem i (4#usize) = .ok r ∧
      UScalar.div i (4#usize) = .ok d ∧
      Array.index_usize weights.PERM r = .ok p ∧
      Array.index_usize weights.PERM d = .ok q ∧
      Array.index_usize c.1 p = .ok x ∧
      Array.index_usize c.2 q = .ok y ∧
      p.val < 4 ∧ q.val < 4 ∧
      p.val < c.1.val.length ∧ q.val < c.2.val.length := by
  obtain ⟨r,d,p,q,x,y,hrem,hdiv,hp,hq,hx,hy,_hr,_hd,hpv,hqv,_hl,_hright⟩ :=
    actual_pair_callback_reads c i hi
  have hpbound4 : p.val < 4 := by
    rw [hpv]
    exact lowPerm_lt4 r.val
  have hqbound4 : q.val < 4 := by
    rw [hqv]
    exact lowPerm_lt4 d.val
  have hlenL : c.1.val.length = 4 := by
    have h := c.1.property
    change c.1.val.length = (4#usize).val at h
    simpa using h
  have hlenR : c.2.val.length = 4 := by
    have h := c.2.property
    change c.2.val.length = (4#usize).val at h
    simpa using h
  refine ⟨r,d,p,q,x,y,hrem,hdiv,hp,hq,hx,hy,hpbound4,hqbound4,?_,?_⟩
  · simpa [hlenL] using hpbound4
  · simpa [hlenR] using hqbound4

/-- The concrete scale used by the actual low callback is the field product
of the pinned QUARTER constant with itself. Its canonical current reducer
value is 2^27 in M31, so the source callback's scaling is explicit. -/
theorem actual_quarter_squared_result :
    ∃ m, actualFieldOps.m31Mul weights.QUARTER weights.QUARTER = .ok m ∧
      m.val = 134217728 ∧ m.val < 2147483647 := by
  obtain ⟨m,hm,hvalue,hbound⟩ :=
    AspisR1.ExtractedCurrentReducer.current_mul_mod
      (536870912#u32) (536870912#u32)
  refine ⟨m, ?_, ?_, ?_⟩
  · unfold actualFieldOps weights.QUARTER
    rw [AspisR1CurrentWide.Proof.m31_mul_same]
    exact hm
  · have hval : m.val = (536870912 * 536870912) % AspisV8R17.RawReducer.P := hvalue
    norm_num [AspisV8R17.RawReducer.P] at hval ⊢
    exact hval
  · have hb : m.val < AspisV8R17.RawReducer.P := hbound
    simpa [AspisV8R17.RawReducer.P] using hb

#print axioms actual_pair_callback_read_bounds
#print axioms actual_quarter_squared_result

end AspisR1PairLowCallCut
