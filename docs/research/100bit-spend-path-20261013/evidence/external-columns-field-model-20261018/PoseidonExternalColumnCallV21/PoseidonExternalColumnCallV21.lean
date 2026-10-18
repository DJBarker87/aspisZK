import PoseidonExternalLazySourceCut
import PoseidonExternalColumnCallEquationV4
import RawPoseidonExtensionWords
import RawPoseidonExternalRowReads
import PoseidonThreeConstantLimbV4
import Aeneas.Std.WP
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1.PoseidonExternalColumnCall
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1.RawPoseidonExternalRowReads
open AspisR1.PoseidonThreeConstantLimb
abbrev State := Array field.QM31 16#usize
abbrev U32 := Std.U32
abbrev U64 := Std.U64
abbrev Closure := state_only_poseidon.external_linear_lazy.closure.closure
abbrev wide := AspisR1.PoseidonThreeConstantLimb.wide

def limbs32 (q : field.QM31) : Array U32 4#usize :=
  Array.make 4#usize [q.c0.a,q.c0.b,q.c1.a,q.c1.b]
def limbAt (q : field.QM31) (j : Usize) (hj : j.val < 4) : U32 :=
  (limbs32 q).val[j.val]'(by simpa [limbs32, Array.make] using hj)

def sumFour (a b c d : U32) : Nat := a.val + b.val + c.val + d.val

theorem external_column_limb_call
    (state : State) (column limb : Usize)
    (hcolumn : column.val < 4) (hlimb : limb.val < 4) :
    ∃ total : U64,
      state_only_poseidon.external_linear_lazy.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
        (state,column) limb = .ok (total,(state,column)) ∧
      total.val = sumFour
        (limbAt (state.val[column.val]'(by have := hcolumn; scalar_tac)) limb hlimb)
        (limbAt (state.val[4+column.val]'(by have := hcolumn; scalar_tac)) limb hlimb)
        (limbAt (state.val[8+column.val]'(by have := hcolumn; scalar_tac)) limb hlimb)
        (limbAt (state.val[12+column.val]'(by have := hcolumn; scalar_tac)) limb hlimb) := by
  have hcolumn' : column.val < 4 := hcolumn
  have h16 : (16#usize).val = 16 := by scalar_tac
  have h4 : (4#usize).val = 4 := by scalar_tac
  let q0 := state.val[column.val]'(by have := hcolumn'; scalar_tac)
  have hidx1Spec : (4#usize + column : Result Usize) ⦃z => z.val = 4 + column.val⦄ := by
    apply UScalar.add_spec
    scalar_tac
  obtain ⟨i1,hi1,hv1⟩ := WP.spec_imp_exists hidx1Spec
  have hidx2Spec : (8#usize + column : Result Usize) ⦃z => z.val = 8 + column.val⦄ := by
    apply UScalar.add_spec
    scalar_tac
  obtain ⟨i2,hi2,hv2⟩ := WP.spec_imp_exists hidx2Spec
  have hidx3Spec : (12#usize + column : Result Usize) ⦃z => z.val = 12 + column.val⦄ := by
    apply UScalar.add_spec
    scalar_tac
  obtain ⟨i3,hi3,hv3⟩ := WP.spec_imp_exists hidx3Spec
  have hq0 : Array.index_usize state column = .ok q0 :=
    array_index_usize_ok state column (by
      have hlt : column.val < 16 := by omega
      simpa [state.property, h16] using hlt)
  have hq1bound : i1.val < 16 := by rw [hv1]; omega
  have hq2bound : i2.val < 16 := by rw [hv2]; omega
  have hq3bound : i3.val < 16 := by rw [hv3]; omega
  let q1 := state.val[i1.val]'(by simpa [state.property, h16] using hq1bound)
  let q2 := state.val[i2.val]'(by simpa [state.property, h16] using hq2bound)
  let q3 := state.val[i3.val]'(by simpa [state.property, h16] using hq3bound)
  have hq1 : Array.index_usize state i1 = .ok q1 := array_index_usize_ok state i1 (by simpa [state.property, h16] using hq1bound)
  have hq2 : Array.index_usize state i2 = .ok q2 := array_index_usize_ok state i2 (by simpa [state.property, h16] using hq2bound)
  have hq3 : Array.index_usize state i3 = .ok q3 := array_index_usize_ok state i3 (by simpa [state.property, h16] using hq3bound)
  have he0 := AspisR1.RawPoseidonExtensionWords.extension_limbs_words q0
  have he1 := AspisR1.RawPoseidonExtensionWords.extension_limbs_words q1
  have he2 := AspisR1.RawPoseidonExtensionWords.extension_limbs_words q2
  have he3 := AspisR1.RawPoseidonExtensionWords.extension_limbs_words q3
  let l0 := limbs32 q0
  let l1 := limbs32 q1
  let l2 := limbs32 q2
  let l3 := limbs32 q3
  have hl0 : Array.index_usize l0 limb = .ok (limbAt q0 limb hlimb) :=
    array_index_usize_ok l0 limb (by simpa [l0,limbs32,Array.make] using hlimb)
  have hl1 : Array.index_usize l1 limb = .ok (limbAt q1 limb hlimb) :=
    array_index_usize_ok l1 limb (by simpa [l1,limbs32,Array.make] using hlimb)
  have hl2 : Array.index_usize l2 limb = .ok (limbAt q2 limb hlimb) :=
    array_index_usize_ok l2 limb (by simpa [l2,limbs32,Array.make] using hlimb)
  have hl3 : Array.index_usize l3 limb = .ok (limbAt q3 limb hlimb) :=
    array_index_usize_ok l3 limb (by simpa [l3,limbs32,Array.make] using hlimb)
  have hl0raw : Array.index_usize (Array.make 4#usize [q0.c0.a,q0.c0.b,q0.c1.a,q0.c1.b]) limb = .ok (limbAt q0 limb hlimb) := by
    simpa [l0,limbs32,Array.make] using hl0
  have hl1raw : Array.index_usize (Array.make 4#usize [q1.c0.a,q1.c0.b,q1.c1.a,q1.c1.b]) limb = .ok (limbAt q1 limb hlimb) := by
    simpa [l1,limbs32,Array.make] using hl1
  have hl2raw : Array.index_usize (Array.make 4#usize [q2.c0.a,q2.c0.b,q2.c1.a,q2.c1.b]) limb = .ok (limbAt q2 limb hlimb) := by
    simpa [l2,limbs32,Array.make] using hl2
  have hl3raw : Array.index_usize (Array.make 4#usize [q3.c0.a,q3.c0.b,q3.c1.a,q3.c1.b]) limb = .ok (limbAt q3 limb hlimb) := by
    simpa [l3,limbs32,Array.make] using hl3
  let w0 := wide (limbAt q0 limb hlimb)
  let w1 := wide (limbAt q1 limb hlimb)
  let w2 := wide (limbAt q2 limb hlimb)
  let w3 := wide (limbAt q3 limb hlimb)
  have hw0 : w0.val = (limbAt q0 limb hlimb).val := by simpa [w0] using wide_value (limbAt q0 limb hlimb)
  have hw1 : w1.val = (limbAt q1 limb hlimb).val := by simpa [w1] using wide_value (limbAt q1 limb hlimb)
  have hw2 : w2.val = (limbAt q2 limb hlimb).val := by simpa [w2] using wide_value (limbAt q2 limb hlimb)
  have hw3 : w3.val = (limbAt q3 limb hlimb).val := by simpa [w3] using wide_value (limbAt q3 limb hlimb)
  have hconv0 : lift (core.convert.num.FromU64U32.from (limbAt q0 limb hlimb)) = .ok w0 := by rfl
  have hconv1 : lift (core.convert.num.FromU64U32.from (limbAt q1 limb hlimb)) = .ok w1 := by rfl
  have hconv2 : lift (core.convert.num.FromU64U32.from (limbAt q2 limb hlimb)) = .ok w2 := by rfl
  have hconv3 : lift (core.convert.num.FromU64U32.from (limbAt q3 limb hlimb)) = .ok w3 := by rfl
  have hadd01 : (w0 + w1 : Result U64) ⦃z => z.val = w0.val + w1.val⦄ := by apply UScalar.add_spec; scalar_tac
  obtain ⟨s01,hs01,hs01v⟩ := WP.spec_imp_exists hadd01
  have hadd012 : (s01 + w2 : Result U64) ⦃z => z.val = s01.val + w2.val⦄ := by apply UScalar.add_spec; scalar_tac
  obtain ⟨s012,hs012,hs012v⟩ := WP.spec_imp_exists hadd012
  have hadd0123 : (s012 + w3 : Result U64) ⦃z => z.val = s012.val + w3.val⦄ := by apply UScalar.add_spec; scalar_tac
  obtain ⟨total,htotal,htotalv⟩ := WP.spec_imp_exists hadd0123
  have hrun : state_only_poseidon.external_linear_lazy.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      (state,column) limb = .ok (total,(state,column)) := by
    rw [AspisR1.PoseidonExternalColumnCallEquationV3.source_eq]
    simp only [hq0, hi1, hq1, hi2, hq2, hi3, hq3,
      he0, he1, he2, he3, hl0raw, hl1raw, hl2raw, hl3raw, hconv0, hconv1, hconv2, hconv3, hs01, hs012, htotal,
      bind_tc_ok]
  have hq1value : q1 = state.val[4+column.val]'(by have := hcolumn'; scalar_tac) := by simp [q1,hv1]
  have hq2value : q2 = state.val[8+column.val]'(by have := hcolumn'; scalar_tac) := by simp [q2,hv2]
  have hq3value : q3 = state.val[12+column.val]'(by have := hcolumn'; scalar_tac) := by simp [q3,hv3]
  refine ⟨total,hrun,?_⟩
  simp only [sumFour,htotalv,hs012v,hs01v,hw0,hw1,hw2,hw3,q0,hq1value,hq2value,hq3value]
#print axioms external_column_limb_call
end AspisR1.PoseidonExternalColumnCall
