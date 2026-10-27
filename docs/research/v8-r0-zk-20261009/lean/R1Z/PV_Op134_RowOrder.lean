import R1Z.PV_Op134_RowSpec
import Mathlib.Data.List.Dedup
namespace R1Z.PV_Op134_RowOrder
open Aeneas Aeneas.Std
set_option autoImplicit false

def good (xs : List U16) (lo hi : Nat) : Prop :=
  xs.Pairwise (fun a b => a.val < b.val) ∧ ∀ r ∈ xs, lo ≤ r.val ∧ r.val < hi

theorem append {xs ys : List U16} {lo mid hi : Nat}
    (hx : good xs lo mid) (hy : good ys mid hi) (hlo : lo ≤ mid) (hhi : mid ≤ hi) :
    good (xs ++ ys) lo hi := by
  constructor
  · exact List.pairwise_append.mpr ⟨hx.1,hy.1,by
      intro a ha b hb; have := hx.2 a ha; have := hy.2 b hb; omega⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · have := hx.2 r hr; omega
    · have := hy.2 r hr; omega
attribute [local irreducible] PV_Op134_Rows00.rows PV_Op134_Rows01.rows PV_Op134_Rows02.rows PV_Op134_Rows03.rows PV_Op134_Rows04.rows PV_Op134_Rows05.rows PV_Op134_Rows06.rows PV_Op134_Rows07.rows PV_Op134_Rows08.rows PV_Op134_Rows09.rows PV_Op134_Rows10.rows PV_Op134_Rows11.rows PV_Op134_Rows12.rows PV_Op134_Rows13.rows
theorem ordered_bounds : good PV_Op134_RowSpec.rows 11 1024 := by
  have b0 : good PV_Op134_Rows00.rows 11 96 := by
    refine ⟨PV_Op134_Rows00.sorted,?_⟩
    intro r hr
    have := PV_Op134_Rows00.bounds r hr
    omega
  have b1 : good PV_Op134_Rows01.rows 96 187 := by
    refine ⟨PV_Op134_Rows01.sorted,?_⟩
    intro r hr
    have := PV_Op134_Rows01.bounds r hr
    omega
  have b2 : good PV_Op134_Rows02.rows 187 268 := by
    refine ⟨PV_Op134_Rows02.sorted,?_⟩
    intro r hr
    have := PV_Op134_Rows02.bounds r hr
    omega
  have b3 : good PV_Op134_Rows03.rows 268 352 := by
    refine ⟨PV_Op134_Rows03.sorted,?_⟩
    intro r hr
    have := PV_Op134_Rows03.bounds r hr
    omega
  have b4 : good PV_Op134_Rows04.rows 352 460 := by
    refine ⟨PV_Op134_Rows04.sorted,?_⟩
    intro r hr
    have := PV_Op134_Rows04.bounds r hr
    omega
  have b5 : good PV_Op134_Rows05.rows 460 571 := by
    refine ⟨PV_Op134_Rows05.sorted,?_⟩
    intro r hr
    have := PV_Op134_Rows05.bounds r hr
    omega
  have b6 : good PV_Op134_Rows06.rows 571 652 := by
    refine ⟨PV_Op134_Rows06.sorted,?_⟩
    intro r hr
    have := PV_Op134_Rows06.bounds r hr
    omega
  have b7 : good PV_Op134_Rows07.rows 652 736 := by
    refine ⟨PV_Op134_Rows07.sorted,?_⟩
    intro r hr
    have := PV_Op134_Rows07.bounds r hr
    omega
  have b8 : good PV_Op134_Rows08.rows 736 827 := by
    refine ⟨PV_Op134_Rows08.sorted,?_⟩
    intro r hr
    have := PV_Op134_Rows08.bounds r hr
    omega
  have b9 : good PV_Op134_Rows09.rows 827 914 := by
    refine ⟨PV_Op134_Rows09.sorted,?_⟩
    intro r hr
    have := PV_Op134_Rows09.bounds r hr
    omega
  have b10 : good PV_Op134_Rows10.rows 914 946 := by
    refine ⟨PV_Op134_Rows10.sorted,?_⟩
    intro r hr
    have := PV_Op134_Rows10.bounds r hr
    omega
  have b11 : good PV_Op134_Rows11.rows 946 978 := by
    refine ⟨PV_Op134_Rows11.sorted,?_⟩
    intro r hr
    have := PV_Op134_Rows11.bounds r hr
    omega
  have b12 : good PV_Op134_Rows12.rows 978 1010 := by
    refine ⟨PV_Op134_Rows12.sorted,?_⟩
    intro r hr
    have := PV_Op134_Rows12.bounds r hr
    omega
  have b13 : good PV_Op134_Rows13.rows 1010 1024 := by
    refine ⟨PV_Op134_Rows13.sorted,?_⟩
    intro r hr
    have := PV_Op134_Rows13.bounds r hr
    omega
  have h12 := append b12 b13 (by decide) (by decide)
  have h11 := append b11 h12 (by decide) (by decide)
  have h10 := append b10 h11 (by decide) (by decide)
  have h9 := append b9 h10 (by decide) (by decide)
  have h8 := append b8 h9 (by decide) (by decide)
  have h7 := append b7 h8 (by decide) (by decide)
  have h6 := append b6 h7 (by decide) (by decide)
  have h5 := append b5 h6 (by decide) (by decide)
  have h4 := append b4 h5 (by decide) (by decide)
  have h3 := append b3 h4 (by decide) (by decide)
  have h2 := append b2 h3 (by decide) (by decide)
  have h1 := append b1 h2 (by decide) (by decide)
  have h0 := append b0 h1 (by decide) (by decide)
  simpa only [PV_Op134_RowSpec.rows,List.append_assoc] using h0

theorem sorted : PV_Op134_RowSpec.rows.Pairwise (fun a b => a.val < b.val) := ordered_bounds.1

theorem nodup : PV_Op134_RowSpec.rows.Nodup := by
  exact sorted.imp (by intro a b h heq; subst b; exact (Nat.lt_irrefl _) h)

theorem dedup : PV_Op134_RowSpec.rows.dedup = PV_Op134_RowSpec.rows := nodup.dedup

#print axioms append
#print axioms ordered_bounds
#print axioms sorted
#print axioms nodup
#print axioms dedup
end R1Z.PV_Op134_RowOrder
