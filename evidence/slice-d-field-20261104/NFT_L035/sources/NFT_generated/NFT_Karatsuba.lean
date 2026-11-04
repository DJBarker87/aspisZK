import NFQ_STAGE2_IMPORT
set_option autoImplicit false
namespace NFT_Karatsuba
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
abbrev C := field.CM31
abbrev Q := field.QM31
abbrev Sums := Array (Array U64 3#usize) 3#usize
abbrev reconstruct := AspisR1PoseidonPreparedSum3Source.field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call

def G (sums : Sums) (mulR : C → Result C) : Result Q := do
  let s0 ← Array.index_usize sums 0#usize
  let m0 ← reconstruct () s0
  let s1 ← Array.index_usize sums 1#usize
  let m1 ← reconstruct () s1
  let s2 ← Array.index_usize sums 2#usize
  let m2 ← reconstruct () s2
  let r ← mulR m1
  let c0 ← field.CM31.add m0 r
  let t ← field.CM31.sub m2 m0
  let c1 ← field.CM31.sub t m1
  ok ⟨c0,c1⟩

theorem source (sums : Sums) : G sums field.mul_by_r=
    AspisR1PoseidonPreparedSum3Source.field.qm31_from_karatsuba_channel_sums sums := by rfl

theorem total (sums : Sums) :
    ∃ out : Q, AspisR1PoseidonPreparedSum3Source.field.qm31_from_karatsuba_channel_sums sums=ok out ∧
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM out :=
  AspisR1PoseidonPreparedKaratsubaSuccess.from_karatsuba_success sums

theorem mul_r_eq_hiding (x : C) : field.mul_by_r x=
    AspisR1SelectedMaskProbe.state_only_hiding.cm31_mul_r x := by
  simp only [field.mul_by_r,AspisR1SelectedMaskProbe.state_only_hiding.cm31_mul_r,
    field.CM31.new,bind_tc_ok,bind_assoc_eq]

theorem mul_r_value (x : C) (canonical : AspisR1.ExtractedMaskTowerAdd.CanonicalCM x) :
    ∃ z : C, field.mul_by_r x=ok z ∧ AspisR1.ExtractedMaskTowerAdd.CanonicalCM z ∧
      z.a.val=(((x.a.val+x.a.val)%2147483647)+2147483647-x.b.val)%2147483647 ∧
      z.b.val=(x.a.val+((x.b.val+x.b.val)%2147483647))%2147483647 := by
  simpa only [mul_r_eq_hiding] using NFQ_Linear.source x canonical

#print axioms source
#print axioms total
#print axioms mul_r_eq_hiding
#print axioms mul_r_value
end NFT_Karatsuba
