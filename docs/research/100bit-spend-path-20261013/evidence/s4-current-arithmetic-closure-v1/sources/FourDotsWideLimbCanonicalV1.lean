import AspisR1FastDotsCurrent.FunsOpsV4
import AspisR1EbyKPushWideToQ

set_option autoImplicit false
open Aeneas Aeneas.Std Result WP

namespace AspisR1FastDotsWideLimbCanonical

abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev U32 := Std.U32
abbrev Limbs := Array U32 8#usize
abbrev P : Nat := 2147483647

def limbArray (x : Wide) : Limbs :=
  Array.make 8#usize
    [x.c0.c0.a, x.c0.c0.b, x.c0.c1.a, x.c0.c1.b,
     x.c1.c0.a, x.c1.c0.b, x.c1.c1.a, x.c1.c1.b]

def CoordinateBound (x : Wide) : Prop :=
  x.c0.c0.a.val < P ∧ x.c0.c0.b.val < P ∧
  x.c0.c1.a.val < P ∧ x.c0.c1.b.val < P ∧
  x.c1.c0.a.val < P ∧ x.c1.c0.b.val < P ∧
  x.c1.c1.a.val < P ∧ x.c1.c1.b.val < P

theorem all_emitted_limb_entries_canonical
    (x : Wide) (hx : CoordinateBound x) :
    ∀ i : Fin 8,
      ((limbArray x).val[i.val]'(by
        simpa [(limbArray x).property] using i.isLt)).val < P := by
  intro i
  rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
  by_cases h0i : i.val = 0
  · have heq : i = ⟨0, by decide⟩ := Fin.ext h0i
    subst i
    simpa [limbArray, Array.make] using h0
  · by_cases h1i : i.val = 1
    · have heq : i = ⟨1, by decide⟩ := Fin.ext h1i
      subst i
      simpa [limbArray, Array.make] using h1
    · by_cases h2i : i.val = 2
      · have heq : i = ⟨2, by decide⟩ := Fin.ext h2i
        subst i
        simpa [limbArray, Array.make] using h2
      · by_cases h3i : i.val = 3
        · have heq : i = ⟨3, by decide⟩ := Fin.ext h3i
          subst i
          simpa [limbArray, Array.make] using h3
        · by_cases h4i : i.val = 4
          · have heq : i = ⟨4, by decide⟩ := Fin.ext h4i
            subst i
            simpa [limbArray, Array.make] using h4
          · by_cases h5i : i.val = 5
            · have heq : i = ⟨5, by decide⟩ := Fin.ext h5i
              subst i
              simpa [limbArray, Array.make] using h5
            · by_cases h6i : i.val = 6
              · have heq : i = ⟨6, by decide⟩ := Fin.ext h6i
                subst i
                simpa [limbArray, Array.make] using h6
              · have h7i : i.val = 7 := by omega
                have heq : i = ⟨7, by decide⟩ := Fin.ext h7i
                subst i
                simpa [limbArray, Array.make] using h7

theorem toLimbs_actual_value (x : Wide) :
    AspisR1EbyKPushWideToQ.toLimbs x = .ok (limbArray x) := by
  rfl

theorem actual_read_is_canonical
    (x : Wide) (hx : CoordinateBound x)
    (i : Usize) (hi : i.val < 8) (y : U32)
    (hread : Array.index_usize (limbArray x) i = .ok y) :
    y.val < P := by
  have hlen : i.val < (limbArray x).val.length := by
    simpa [(limbArray x).property] using hi
  obtain ⟨q, hreadq, hqvalue⟩ :=
    WP.spec_imp_exists (Array.index_usize_spec (limbArray x) i hlen)
  have hqy : q = y := Result.ok.inj (hreadq.symm.trans hread)
  have hy : y = (limbArray x).val[i.val]'hlen := by simpa [hqy] using hqvalue
  have hmember : y ∈ (limbArray x).val := by
    rw [hy]
    exact List.getElem_mem hlen
  rcases hx with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
  simp [limbArray, Array.make] at hmember
  rcases hmember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem bound_for_actual_wideToLimbs
    (x : Wide) (hx : CoordinateBound x)
    (a : Limbs) (ha : AspisR1EbyKPushWideToQ.toLimbs x = .ok a)
    (i : Usize) (hi : i.val < 8) (y : U32)
    (hread : Array.index_usize a i = .ok y) :
    y.val < P := by
  have ha' : a = limbArray x := Result.ok.inj (ha.symm.trans (toLimbs_actual_value x))
  subst a
  exact actual_read_is_canonical x hx i hi y hread

#print axioms toLimbs_actual_value
#print axioms all_emitted_limb_entries_canonical
#print axioms actual_read_is_canonical
#print axioms bound_for_actual_wideToLimbs

end AspisR1FastDotsWideLimbCanonical
