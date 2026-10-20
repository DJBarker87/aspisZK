import FibrePointDecodedProduct
import R17ActualWholeTablePower
import R17TableCirclePowerBridge
import AspisFormal.V7ExactOneFoldDomains
import AspisFormal.V6EncoderDistance

open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace R17FibrePointStoredDomain
open AspisR1QueryGeometryActual AspisCircleGroupOrder AspisV7ExactOneFoldDomains AspisV5ComponentCConcreteFoldLinearity

abbrev P := 2147483647

def tableEntryZC (p : Std.U32 × Std.U32) : R17TableBasePowerBridge.ZC :=
  ⟨(p.1.val : ZMod P), (p.2.val : ZMod P)⟩

theorem decodeEntry_eq_tableEntryZC (p : Std.U32 × Std.U32) :
    R17FibrePointDecodedProduct.decodeEntry p =
      ((tableEntryZC p).re, (tableEntryZC p).im) := by
  cases p
  rfl

theorem tablePairExponent_eq_storedInt (i : Fin 262144) :
    ((2 ^ 10 + 2 ^ 12 *
      AspisV5FriBitReverse.reverseBits 18 i.val : Nat) : Int) =
      AspisV6EncoderDistance.initialCircleExponent
        (AspisV7ExactOneFoldDomains.storedInitialNaturalIndex20
          (AspisV5ComponentCConcreteFoldLinearity.childIndex i 0)) := by
  simp only [AspisV7ExactOneFoldDomains.storedInitialNaturalIndex20_child_zero,
    AspisV6EncoderDistance.initialCircleExponent,
    AspisV5FriBitReverse.reverseFin, Fin.val_mk]
  push_cast
  ring

/-- Successful execution of the extracted fibre-point source body, together
with the exact source mask/shift indices and the retained CM31 operation laws,
returns the maintained stored fibre point. The table lookups below are the
actual extracted arrays and their all-index power certificates. -/
theorem successful_fibre_point_eq_stored
    (ops : CM31Ops) (hspec : R17FibrePointDecodedProduct.CM31OpsSemantics ops)
    (u : domain.FibreIndex) (hu : u.val < 262144)
    (ix iA iB : Std.Usize)
    (entryA entryB : Std.U32 × Std.U32)
    (left right product : field.CM31)
    (hget : domain.FibreIndex.get u = .ok ix)
    (hix : ix.val = u.val)
    (hmask : lift (ix &&& 511#usize) = .ok iA)
    (hia : iA.val = ix.val % 512)
    (hlookupA : Array.index_usize fast_domain.TABLE_A iA = .ok entryA)
    (hleft : fast_domain.table_value ops entryA = .ok left)
    (hshift : ix >>> 9#i32 = .ok iB)
    (hib : iB.val = ix.val / 512)
    (hlookupB : Array.index_usize fast_domain.TABLE_B iB = .ok entryB)
    (hright : fast_domain.table_value ops entryB = .ok right)
    (hmul : ops.mul left right = .ok product) :
    fast_domain.fibre_point ops u = .ok
      ({ x := product.a, y := product.b } : domain.Point field.M31) ∧
    (⟨(R17FibrePointDecodedProduct.decodePoint
        ({ x := product.a, y := product.b } : domain.Point field.M31)).1,
      (R17FibrePointDecodedProduct.decodePoint
        ({ x := product.a, y := product.b } : domain.Point field.M31)).2⟩ :
      R17TableBasePowerBridge.ZC) =
      R17TableCirclePowerBridge.circleCoords
        (AspisV7ExactOneFoldDomains.storedInitialFibrePoint20
          (⟨u.val, hu⟩ : Fin 262144)) := by

  let i : Fin 262144 := ⟨u.val, hu⟩
  have hiA : iA.val < 512 := by rw [hia, hix]; omega
  have hiB : iB.val < 512 := by rw [hib, hix]; omega
  have hsplit : u.val = 512 * iB.val + iA.val := by
    rw [hia, hib, hix]
    have h := Nat.mod_add_div ix.val 512
    omega
  have hprod := R17FibrePointDecodedProduct.successful_fibre_point_decodes_to_product
    ops hspec u ix iA iB entryA entryB left right product
    hget hmask hlookupA hleft hshift hlookupB hright hmul
  have htable := R17ActualWholeTablePower.actual_table_pair_product
    iA iB hiA hiB entryA entryB hlookupA hlookupB
  have hdecodeA : tableEntryZC entryA =
      R17TableBasePowerBridge.decode
        (R17TableAChunk00Certificate.toNatC
          (⟨entryA.1.val, entryA.2.val⟩ : R17TableBasePowerProbe.C)) := by
    cases entryA
    rfl
  have hdecodeB : tableEntryZC entryB =
      R17TableBasePowerBridge.decode
        (R17TableBChunk00Certificate.toNatC
          (⟨entryB.1.val, entryB.2.val⟩ : R17TableBasePowerProbe.C)) := by
    cases entryB
    rfl
  have hentryA : R17FibrePointDecodedProduct.decodeEntry entryA =
      ((tableEntryZC entryA).re, (tableEntryZC entryA).im) := by
    cases entryA
    rfl
  have hentryB : R17FibrePointDecodedProduct.decodeEntry entryB =
      ((tableEntryZC entryB).re, (tableEntryZC entryB).im) := by
    cases entryB
    rfl
  have hprodEntries := hprod.2
  rw [hentryA, hentryB] at hprodEntries
  have hcoord :
      (⟨(R17FibrePointDecodedProduct.decodePoint
          ({ x := product.a, y := product.b } : domain.Point field.M31)).1,
        (R17FibrePointDecodedProduct.decodePoint
          ({ x := product.a, y := product.b } : domain.Point field.M31)).2⟩ :
        R17TableBasePowerBridge.ZC) =
      R17TableBasePowerBridge.zMul (tableEntryZC entryA) (tableEntryZC entryB) := by
    apply R17TableBasePowerBridge.ZC.ext
    · simpa [R17FibrePointDecodedProduct.cm31Product,
        R17FibrePointDecodedProduct.P, R17TableBasePowerBridge.P,
        R17TableBasePowerBridge.zMul, tableEntryZC] using
        congrArg Prod.fst hprodEntries
    · simpa [R17FibrePointDecodedProduct.cm31Product,
        R17FibrePointDecodedProduct.P, R17TableBasePowerBridge.P,
        R17TableBasePowerBridge.zMul, tableEntryZC] using
        congrArg Prod.snd hprodEntries
  have hresPower :
      (⟨(R17FibrePointDecodedProduct.decodePoint
          ({ x := product.a, y := product.b } : domain.Point field.M31)).1,
        (R17FibrePointDecodedProduct.decodePoint
          ({ x := product.a, y := product.b } : domain.Point field.M31)).2⟩ :
        R17TableBasePowerBridge.ZC) =
      R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode
          (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
        (2 ^ 10 + 2 ^ 12 * AspisV5FriBitReverse.reverseBits 18 u.val) := by
    calc
      _ = R17TableBasePowerBridge.zMul (tableEntryZC entryA) (tableEntryZC entryB) := hcoord
      _ = R17TableBasePowerBridge.zMul
            (R17TableBasePowerBridge.decode
              (R17TableAChunk00Certificate.toNatC
                (⟨entryA.1.val, entryA.2.val⟩ : R17TableBasePowerProbe.C)))
            (R17TableBasePowerBridge.decode
              (R17TableBChunk00Certificate.toNatC
                (⟨entryB.1.val, entryB.2.val⟩ : R17TableBasePowerProbe.C))) := by
              rw [hdecodeA, hdecodeB]
      _ = R17TableBasePowerBridge.zPow
            (R17TableBasePowerBridge.decode
              (R17TableAChunk00Certificate.toNatC R17TableBasePowerProbe.gen))
            (2 ^ 10 + 2 ^ 12 * AspisV5FriBitReverse.reverseBits 18 u.val) := by
              rw [hsplit]
              exact htable
  have hcoordPower :
      (⟨(R17FibrePointDecodedProduct.decodePoint
          ({ x := product.a, y := product.b } : domain.Point field.M31)).1,
        (R17FibrePointDecodedProduct.decodePoint
          ({ x := product.a, y := product.b } : domain.Point field.M31)).2⟩ :
        R17TableBasePowerBridge.ZC) =
      R17TableCirclePowerBridge.circleCoords
        (AspisCircleGroupOrder.g ^
          (2 ^ 10 + 2 ^ 12 * AspisV5FriBitReverse.reverseBits 18 u.val)) := by
    rw [hresPower, R17TableCirclePowerBridge.residuePower_eq_circlePower]
  have hstoredExp := tablePairExponent_eq_storedInt i
  have hstoredPow :
      (AspisCircleGroupOrder.g ^
        (2 ^ 10 + 2 ^ 12 * AspisV5FriBitReverse.reverseBits 18 u.val)) =
      AspisV7ExactOneFoldDomains.storedInitialFibrePoint20 i := by
    rw [AspisV7ExactOneFoldDomains.storedInitialFibrePoint20_eq_zpow]
    rw [← zpow_natCast]
    exact congrArg (fun e : Int => AspisCircleGroupOrder.g ^ e) hstoredExp
  have hfinal := hcoordPower
  rw [hstoredPow] at hfinal
  constructor
  · exact hprod.1
  · exact hfinal

#print axioms tablePairExponent_eq_storedInt
#print axioms successful_fibre_point_eq_stored

end R17FibrePointStoredDomain
