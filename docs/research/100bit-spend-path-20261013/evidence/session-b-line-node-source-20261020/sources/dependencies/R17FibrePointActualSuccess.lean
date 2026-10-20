import R17FibrePointStoredDomain
import R17ActualTableArrayIndexV1
import Init.Data.Nat.Bitwise.Lemmas

open Aeneas Aeneas.Std Result ControlFlow Error WP
set_option autoImplicit false

namespace R17FibrePointActualSuccess
open AspisR1QueryGeometryActual

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β} {x : β}
    (h : Bind.bind r f = .ok x) : ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

private theorem mask9_success (ix : Usize) :
    ∃ iA : Usize, lift (ix &&& 511#usize) = .ok iA ∧ iA.val = ix.val % 512 := by
  obtain ⟨iA, hrun, hspec⟩ := WP.spec_imp_exists (UScalar.and_spec ix (511#usize))
  refine ⟨iA, hrun, ?_⟩
  have h511 : (511#usize).val = 511 := by rfl
  have hval : (ix &&& 511#usize).val = ix.val % 512 := by
    rw [UScalar.val_and, h511]
    simpa only [show (512 : Nat) = 2 ^ 9 by norm_num] using
      (Nat.and_two_pow_sub_one_eq_mod ix.val 9)
  exact hspec.1.trans hval

private theorem shift9_success (ix : Usize) :
    ∃ iB : Usize, ix >>> 9#i32 = .ok iB ∧ iB.val = ix.val / 512 := by
  have hy0 : 0 ≤ (9#i32).val := by norm_num
  have hy1 : (9#i32).val < UScalarTy.Usize.numBits := by
    cases System.Platform.numBits_eq <;>
      norm_num [UScalarTy.Usize_numBits_eq, *]
  have hspec := UScalar.ShiftRight_IScalar_spec ix (9#i32) hy0 hy1
  obtain ⟨iB, hrun, ⟨hval, _⟩⟩ := WP.spec_imp_exists hspec
  refine ⟨iB, hrun, ?_⟩
  rw [hval]
  simp [IScalar.toNat, Nat.shiftRight_eq_div_pow]

/-- The concrete `FibreIndex` get, low-nine-bit mask, high-bit shift, and
bounded table reads all succeed for every valid 18-bit source index. -/
theorem source_indices_and_table_reads (u : domain.FibreIndex) (hu : u.val < 262144) :
    ∃ ix iA iB entryA entryB,
      domain.FibreIndex.get u = .ok ix ∧ ix.val = u.val ∧
      lift (ix &&& 511#usize) = .ok iA ∧ iA.val = u.val % 512 ∧
      ix >>> 9#i32 = .ok iB ∧ iB.val = u.val / 512 ∧
      Array.index_usize fast_domain.TABLE_A iA = .ok entryA ∧
      Array.index_usize fast_domain.TABLE_B iB = .ok entryB := by
  let ix : Usize := u
  have hget : domain.FibreIndex.get u = .ok ix := rfl
  have hix : ix.val = u.val := rfl
  obtain ⟨iA, hmask, hia⟩ := mask9_success ix
  obtain ⟨iB, hshift, hib⟩ := shift9_success ix
  have hiaU : iA.val = u.val % 512 := by rw [hia, hix]
  have hibU : iB.val = u.val / 512 := by rw [hib, hix]
  have hiA : iA.val < 512 := by rw [hiaU]; exact Nat.mod_lt _ (by omega)
  have hiB : iB.val < 512 := by rw [hibU]; omega
  let entryA := fast_domain.TABLE_A_entries[iA.val]'(by
    rw [fast_domain.TABLE_A_entries_length]
    exact hiA)
  let entryB := fast_domain.TABLE_B_entries[iB.val]'(by
    rw [fast_domain.TABLE_B_entries_length]
    exact hiB)
  have hlookupA := R17ActualTableArrayIndexV1.tableA_index_entries iA hiA
  have hlookupB := R17ActualTableArrayIndexV1.tableB_index_entries iB hiB
  exact ⟨ix, iA, iB, entryA, entryB, hget, hix, hmask, hiaU, hshift,
    hibU, hlookupA, hlookupB⟩

/-- Inverting a successful actual source call supplies every monadic stage;
source-index arithmetic is then obtained from the actual Usize operations.
Only the explicit CM31 operation semantics and valid-index premise remain. -/
theorem successful_call_eq_stored
    (ops : CM31Ops) (hspec : R17FibrePointDecodedProduct.CM31OpsSemantics ops)
    (u : domain.FibreIndex) (hu : u.val < 262144)
    (point : domain.Point field.M31)
    (hcall : fast_domain.fibre_point ops u = .ok point) :
    (⟨(R17FibrePointDecodedProduct.decodePoint point).1,
       (R17FibrePointDecodedProduct.decodePoint point).2⟩ :
       R17TableBasePowerBridge.ZC) =
      R17TableCirclePowerBridge.circleCoords
        (AspisV7ExactOneFoldDomains.storedInitialFibrePoint20
          (⟨u.val, hu⟩ : Fin 262144)) := by
  have h := hcall
  unfold fast_domain.fibre_point at h
  rcases bind_ok_inv h with ⟨ix, hget, hrest1⟩
  rcases bind_ok_inv hrest1 with ⟨iA, hmask, hrest2⟩
  rcases bind_ok_inv hrest2 with ⟨entryA, hlookupA, hrest3⟩
  rcases bind_ok_inv hrest3 with ⟨left, hleft, hrest4⟩
  rcases bind_ok_inv hrest4 with ⟨iB, hshift, hrest5⟩
  rcases bind_ok_inv hrest5 with ⟨entryB, hlookupB, hrest6⟩
  rcases bind_ok_inv hrest6 with ⟨right, hright, hrest7⟩
  rcases bind_ok_inv hrest7 with ⟨product, hmul, hfinal⟩
  have hpoint : ({ x := product.a, y := product.b } : domain.Point field.M31) = point :=
    Result.ok.inj hfinal
  subst point
  have ⟨ix0, iA0, iB0, entryA0, entryB0,
      hget0, hix0, hmask0, hia0, hshift0, hib0, hlookupA0, hlookupB0⟩ :=
    source_indices_and_table_reads u hu
  have hixeq : ix = ix0 := Result.ok.inj (hget.symm.trans hget0)
  subst ix
  have hiaeq : iA0 = iA := Result.ok.inj (hmask0.symm.trans hmask)
  subst iA
  have hia : iA0.val = ix0.val % 512 := by
    calc
      iA0.val = u.val % 512 := hia0
      _ = ix0.val % 512 := by rw [hix0]
  have hibeq : iB0 = iB := Result.ok.inj (hshift0.symm.trans hshift)
  subst iB
  have hib : iB0.val = ix0.val / 512 := by
    calc
      iB0.val = u.val / 512 := hib0
      _ = ix0.val / 512 := by rw [hix0]
  have hiA : iA0.val < 512 := by rw [hia0]; exact Nat.mod_lt _ (by omega)
  have hiB : iB0.val < 512 := by rw [hib0]; omega
  have hentryAeq : entryA = entryA0 := Result.ok.inj (hlookupA.symm.trans hlookupA0)
  have hentryBeq : entryB = entryB0 := Result.ok.inj (hlookupB.symm.trans hlookupB0)
  subst entryA
  subst entryB
  obtain ⟨_, hcoord⟩ := R17FibrePointStoredDomain.successful_fibre_point_eq_stored
    ops hspec u hu ix0 iA0 iB0 entryA0 entryB0 left right product
    hget0 hix0 hmask0 hia hlookupA0 hleft hshift0 hib hlookupB0 hright hmul
  exact hcoord

#print axioms source_indices_and_table_reads
#print axioms successful_call_eq_stored
end R17FibrePointActualSuccess
