import RPv_AspisR1_PoseidonPreparedProductCast
import RPv_AspisR1_PoseidonPreparedLeftCellValues
import RPv_AspisR1_PoseidonPreparedTableCellValues
import RPv_AspisR1_PoseidonPreparedSum3DecodedWithBuild
import ExtractedMaskPreparedState

set_option autoImplicit false
namespace AspisR1.PoseidonPreparedProductCells
open Aeneas.Std Result AspisR1SelectedMaskProbe
open AspisV8R15.ExactTowerBase

abbrev M := AspisV8R15.ExactTowerBase.M31Exact
abbrev CMExact := AspisV8R15.ExactTowerBase.CM31Exact
abbrev QM := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev PreparedArray := Array Prepared 3#usize
abbrev RightArray := Array QM 3#usize
abbrev Components := Array (Array field.M31 3#usize) 3#usize
abbrev CanonicalQM := AspisR1.ExtractedMaskTowerAdd.CanonicalQM

private def leftAt (left : PreparedArray) (i : Fin 3) : Prepared :=
  left.val[(AspisR1PoseidonPreparedIndexProductBounds.uFin i).val]'(by
    have hu := AspisR1PoseidonPreparedIndexProductBounds.uFin_val i
    simpa [left.property, hu] using i.isLt)

private def rightAt (right : RightArray) (i : Fin 3) : QM :=
  right.val[(AspisR1PoseidonPreparedIndexProductBounds.uFin i).val]'(by
    have hu := AspisR1PoseidonPreparedIndexProductBounds.uFin_val i
    simpa [right.property, hu] using i.isLt)

private def at3 {α : Type} (a : Array α 3#usize) (i : Usize) (hi : i.val < 3) : α :=
  AspisR1PoseidonPreparedChannelRunStepLocal.at3 a i hi

private def leftCell (left : PreparedArray) (index component channel : Usize)
    (hi : index.val < 3) (hc : component.val < 3) (hch : channel.val < 3) : field.M31 :=
  at3 (at3 (at3 left index hi).components component hc) channel hch

private def tableCell (table : Components) (component channel : Usize)
    (hc : component.val < 3) (hch : channel.val < 3) : field.M31 :=
  at3 (at3 table component hc) channel hch

def rightBuilder (q : QM) : Result Components := do
  let rightSum ← field.CM31.add q.c0 q.c1
  let m0 ← field.M31.add q.c0.a q.c0.b
  let m1 ← field.M31.add q.c1.a q.c1.b
  let m2 ← field.M31.add rightSum.a rightSum.b
  ok (Array.make 3#usize [
    (Array.make 3#usize [q.c0.a,q.c0.b,m0] : Array field.M31 3#usize),
    (Array.make 3#usize [q.c1.a,q.c1.b,m1] : Array field.M31 3#usize),
    (Array.make 3#usize [rightSum.a,rightSum.b,m2] : Array field.M31 3#usize)] : Components)

theorem product_cells (left : PreparedArray) (tables : Fin 3 → Components)
    (right : RightArray) (i : Fin 3) (x : QM)
    (hprepared : AspisR1.ExtractedMaskPreparedState.PreparedFor (leftAt left i) x)
    (hx : CanonicalQM x)
    (hq : CanonicalQM (rightAt right i))
    (hbuild : rightBuilder (rightAt right i) = .ok (tables i)) :
    let u := AspisR1PoseidonPreparedIndexProductBounds.uFin i
    let p := AspisR1PoseidonPreparedIndexProductBounds.product
    ((p left tables i 0#usize 0#usize (by scalar_tac) (by scalar_tac) : Nat) : M) =
      (x.c0.a.val : M) * ((rightAt right i).c0.a.val : M) ∧
    ((p left tables i 0#usize 1#usize (by scalar_tac) (by scalar_tac) : Nat) : M) =
      (x.c0.b.val : M) * ((rightAt right i).c0.b.val : M) ∧
    ((p left tables i 0#usize 2#usize (by scalar_tac) (by scalar_tac) : Nat) : M) =
      ((x.c0.a.val : M) + (x.c0.b.val : M)) *
        ((rightAt right i).c0.a.val + (rightAt right i).c0.b.val : M) ∧
    ((p left tables i 1#usize 0#usize (by scalar_tac) (by scalar_tac) : Nat) : M) =
      (x.c1.a.val : M) * ((rightAt right i).c1.a.val : M) ∧
    ((p left tables i 1#usize 1#usize (by scalar_tac) (by scalar_tac) : Nat) : M) =
      (x.c1.b.val : M) * ((rightAt right i).c1.b.val : M) ∧
    ((p left tables i 1#usize 2#usize (by scalar_tac) (by scalar_tac) : Nat) : M) =
      ((x.c1.a.val : M) + (x.c1.b.val : M)) *
        ((rightAt right i).c1.a.val + (rightAt right i).c1.b.val : M) ∧
    ((p left tables i 2#usize 0#usize (by scalar_tac) (by scalar_tac) : Nat) : M) =
      ((x.c0.a.val : M) + (x.c1.a.val : M)) *
        ((rightAt right i).c0.a.val + (rightAt right i).c1.a.val : M) ∧
    ((p left tables i 2#usize 1#usize (by scalar_tac) (by scalar_tac) : Nat) : M) =
      ((x.c0.b.val : M) + (x.c1.b.val : M)) *
        ((rightAt right i).c0.b.val + (rightAt right i).c1.b.val : M) ∧
    ((p left tables i 2#usize 2#usize (by scalar_tac) (by scalar_tac) : Nat) : M) =
      (((x.c0.a.val : M) + (x.c0.b.val : M)) +
        (x.c1.a.val : M) + (x.c1.b.val : M)) *
      (((rightAt right i).c0.a.val : M) + (rightAt right i).c0.b.val +
        (rightAt right i).c1.a.val + (rightAt right i).c1.b.val) := by
  dsimp
  obtain ⟨t,s0,s1,s2,hsum,l00,l01,l02,l10,l11,l12,l20,l21,l22,hs0,hs1,hs2⟩ :=
    AspisR1.PoseidonPreparedLeftCellValues.left_cells left i x hprepared
  obtain ⟨rs,m0,m1,m2,hrsum,hm0,hm1,hm2,r00,r01,r02,r10,r11,r12,r20,r21,r22⟩ :=
    AspisR1.PoseidonPreparedTableCellValues.table_cells (rightAt right i) hq (tables i) hbuild
  have hs0' : (s0.val : M) = (x.c0.a.val : M) + (x.c0.b.val : M) := by
    rw [hs0, ZMod.natCast_mod, Nat.cast_add]
  have hs1' : (s1.val : M) = (x.c1.a.val : M) + (x.c1.b.val : M) := by
    rw [hs1, ZMod.natCast_mod, Nat.cast_add]
  have hs2' : (s2.val : M) = (t.a.val : M) + (t.b.val : M) := by
    rw [hs2, ZMod.natCast_mod, Nat.cast_add]
  have hr0' : (m0.val : M) = ((rightAt right i).c0.a.val : M) + ((rightAt right i).c0.b.val : M) := by
    obtain ⟨v,hv,hvval⟩ := AspisR1.PoseidonPreparedFieldArithmetic.m31_add_decode
      (rightAt right i).c0.a (rightAt right i).c0.b hq.1.1 hq.1.2
    have heq : v = m0 := Result.ok.inj (hv.symm.trans hm0)
    rw [← heq]
    exact hvval
  have hr1' : (m1.val : M) = ((rightAt right i).c1.a.val : M) + ((rightAt right i).c1.b.val : M) := by
    obtain ⟨v,hv,hvval⟩ := AspisR1.PoseidonPreparedFieldArithmetic.m31_add_decode
      (rightAt right i).c1.a (rightAt right i).c1.b hq.2.1 hq.2.2
    have heq : v = m1 := Result.ok.inj (hv.symm.trans hm1)
    rw [← heq]
    exact hvval
  obtain ⟨t'', ht'', htval⟩ := AspisR1.PoseidonPreparedFieldArithmetic.cm_add_decode
    x.c0 x.c1 hx.1 hx.2
  have htEq' : t'' = t := Result.ok.inj (ht''.symm.trans hsum)
  have htDecode : AspisR1.PoseidonPreparedFieldArithmetic.decodeCM t =
      AspisR1.PoseidonPreparedFieldArithmetic.decodeCM x.c0 +
        AspisR1.PoseidonPreparedFieldArithmetic.decodeCM x.c1 := by
    rw [← htEq']
    exact htval
  have htA : (t.a.val : M) = (x.c0.a.val : M) + (x.c1.a.val : M) := by
    have h := congrArg (fun z : CMExact => z.re) htDecode
    exact h
  have htB : (t.b.val : M) = (x.c0.b.val : M) + (x.c1.b.val : M) := by
    have h := congrArg (fun z : CMExact => z.im) htDecode
    exact h
  obtain ⟨rs',hrs',hrscan,_,_⟩ := AspisR1.ExtractedMaskTowerAdd.current_cm_add_mod
    (rightAt right i).c0 (rightAt right i).c1 hq.1 hq.2
  have hrsEq : rs' = rs := Result.ok.inj (hrs'.symm.trans hrsum)
  have hrsCan : AspisR1.ExtractedMaskTowerAdd.CanonicalCM rs := by
    simpa [hrsEq] using hrscan
  have hrsDecode : AspisR1.PoseidonPreparedFieldArithmetic.decodeCM rs =
      AspisR1.PoseidonPreparedFieldArithmetic.decodeCM (rightAt right i).c0 +
        AspisR1.PoseidonPreparedFieldArithmetic.decodeCM (rightAt right i).c1 := by
    obtain ⟨v,hv,hvval⟩ := AspisR1.PoseidonPreparedFieldArithmetic.cm_add_decode
      (rightAt right i).c0 (rightAt right i).c1 hq.1 hq.2
    have heq : v = rs := Result.ok.inj (hv.symm.trans hrsum)
    rw [← heq]
    exact hvval
  have hrsA : (rs.a.val : M) = ((rightAt right i).c0.a.val : M) + ((rightAt right i).c1.a.val : M) := by
    exact congrArg (fun z : CMExact => z.re) hrsDecode
  have hrsB : (rs.b.val : M) = ((rightAt right i).c0.b.val : M) + ((rightAt right i).c1.b.val : M) := by
    exact congrArg (fun z : CMExact => z.im) hrsDecode
  have hr2' : (m2.val : M) = (rs.a.val : M) + (rs.b.val : M) := by
    obtain ⟨v,hv,hvval⟩ := AspisR1.PoseidonPreparedFieldArithmetic.m31_add_decode
      rs.a rs.b hrsCan.1 hrsCan.2
    have heq : v = m2 := Result.ok.inj (hv.symm.trans hm2)
    rw [← heq]
    exact hvval
  have hleftTotal : (s2.val : M) =
      ((x.c0.a.val : M) + x.c0.b.val) + x.c1.a.val + x.c1.b.val := by
    rw [hs2', htA, htB]
    ring
  have hrightTotal : (m2.val : M) =
      (((rightAt right i).c0.a.val : M) + (rightAt right i).c0.b.val) +
        (rightAt right i).c1.a.val + (rightAt right i).c1.b.val := by
    rw [hr2', hrsA, hrsB]
    ring
  have hp00 : ((AspisR1PoseidonPreparedIndexProductBounds.product left tables i 0#usize 0#usize
      (by scalar_tac) (by scalar_tac) : Nat) : M) =
      (x.c0.a.val : M) * ((rightAt right i).c0.a.val : M) := by
    apply AspisR1.PoseidonPreparedProductCast.product_cast_eq
    · change leftCell left (AspisR1PoseidonPreparedIndexProductBounds.uFin i) 0#usize 0#usize _ _ _ = _
      exact l00
    · change tableCell (tables i) 0#usize 0#usize _ _ = _
      exact r00
  have hp01 : ((AspisR1PoseidonPreparedIndexProductBounds.product left tables i 0#usize 1#usize
      (by scalar_tac) (by scalar_tac) : Nat) : M) =
      (x.c0.b.val : M) * ((rightAt right i).c0.b.val : M) := by
    apply AspisR1.PoseidonPreparedProductCast.product_cast_eq
    · change leftCell left (AspisR1PoseidonPreparedIndexProductBounds.uFin i) 0#usize 1#usize _ _ _ = _
      exact l01
    · change tableCell (tables i) 0#usize 1#usize _ _ = _
      exact r01
  have hp02 : ((AspisR1PoseidonPreparedIndexProductBounds.product left tables i 0#usize 2#usize
      (by scalar_tac) (by scalar_tac) : Nat) : M) =
      ((x.c0.a.val : M) + x.c0.b.val) *
        ((rightAt right i).c0.a.val + (rightAt right i).c0.b.val : M) := by
    calc
      _ = (s0.val : M) * (m0.val : M) := AspisR1.PoseidonPreparedProductCast.product_cast_eq
        left tables i 0#usize 2#usize (by scalar_tac) (by scalar_tac) s0 m0
        (by change leftCell left (AspisR1PoseidonPreparedIndexProductBounds.uFin i) 0#usize 2#usize _ _ _ = _; exact l02)
        (by change tableCell (tables i) 0#usize 2#usize _ _ = _; exact r02)
      _ = _ := by rw [hs0', hr0']
  have hp10 : ((AspisR1PoseidonPreparedIndexProductBounds.product left tables i 1#usize 0#usize
      (by scalar_tac) (by scalar_tac) : Nat) : M) =
      (x.c1.a.val : M) * ((rightAt right i).c1.a.val : M) := by
    apply AspisR1.PoseidonPreparedProductCast.product_cast_eq
    · change leftCell left (AspisR1PoseidonPreparedIndexProductBounds.uFin i) 1#usize 0#usize _ _ _ = _
      exact l10
    · change tableCell (tables i) 1#usize 0#usize _ _ = _
      exact r10
  have hp11 : ((AspisR1PoseidonPreparedIndexProductBounds.product left tables i 1#usize 1#usize
      (by scalar_tac) (by scalar_tac) : Nat) : M) =
      (x.c1.b.val : M) * ((rightAt right i).c1.b.val : M) := by
    apply AspisR1.PoseidonPreparedProductCast.product_cast_eq
    · change leftCell left (AspisR1PoseidonPreparedIndexProductBounds.uFin i) 1#usize 1#usize _ _ _ = _
      exact l11
    · change tableCell (tables i) 1#usize 1#usize _ _ = _
      exact r11
  have hp12 : ((AspisR1PoseidonPreparedIndexProductBounds.product left tables i 1#usize 2#usize
      (by scalar_tac) (by scalar_tac) : Nat) : M) =
      ((x.c1.a.val : M) + x.c1.b.val) *
        ((rightAt right i).c1.a.val + (rightAt right i).c1.b.val : M) := by
    calc
      _ = (s1.val : M) * (m1.val : M) := AspisR1.PoseidonPreparedProductCast.product_cast_eq
        left tables i 1#usize 2#usize (by scalar_tac) (by scalar_tac) s1 m1
        (by change leftCell left (AspisR1PoseidonPreparedIndexProductBounds.uFin i) 1#usize 2#usize _ _ _ = _; exact l12)
        (by change tableCell (tables i) 1#usize 2#usize _ _ = _; exact r12)
      _ = _ := by rw [hs1', hr1']
  have hp20 : ((AspisR1PoseidonPreparedIndexProductBounds.product left tables i 2#usize 0#usize
      (by scalar_tac) (by scalar_tac) : Nat) : M) =
      ((x.c0.a.val : M) + x.c1.a.val) *
        ((rightAt right i).c0.a.val + (rightAt right i).c1.a.val : M) := by
    calc
      _ = (t.a.val : M) * (rs.a.val : M) := AspisR1.PoseidonPreparedProductCast.product_cast_eq
        left tables i 2#usize 0#usize (by scalar_tac) (by scalar_tac) t.a rs.a
        (by change leftCell left (AspisR1PoseidonPreparedIndexProductBounds.uFin i) 2#usize 0#usize _ _ _ = _; exact l20)
        (by change tableCell (tables i) 2#usize 0#usize _ _ = _; exact r20)
      _ = _ := by rw [htA, hrsA]
  have hp21 : ((AspisR1PoseidonPreparedIndexProductBounds.product left tables i 2#usize 1#usize
      (by scalar_tac) (by scalar_tac) : Nat) : M) =
      ((x.c0.b.val : M) + x.c1.b.val) *
        ((rightAt right i).c0.b.val + (rightAt right i).c1.b.val : M) := by
    calc
      _ = (t.b.val : M) * (rs.b.val : M) := AspisR1.PoseidonPreparedProductCast.product_cast_eq
        left tables i 2#usize 1#usize (by scalar_tac) (by scalar_tac) t.b rs.b
        (by change leftCell left (AspisR1PoseidonPreparedIndexProductBounds.uFin i) 2#usize 1#usize _ _ _ = _; exact l21)
        (by change tableCell (tables i) 2#usize 1#usize _ _ = _; exact r21)
      _ = _ := by rw [htB, hrsB]
  have hp22 : ((AspisR1PoseidonPreparedIndexProductBounds.product left tables i 2#usize 2#usize
      (by scalar_tac) (by scalar_tac) : Nat) : M) =
      (((x.c0.a.val : M) + x.c0.b.val) + x.c1.a.val + x.c1.b.val) *
      (((rightAt right i).c0.a.val : M) + (rightAt right i).c0.b.val +
        (rightAt right i).c1.a.val + (rightAt right i).c1.b.val) := by
    calc
      _ = (s2.val : M) * (m2.val : M) := AspisR1.PoseidonPreparedProductCast.product_cast_eq
        left tables i 2#usize 2#usize (by scalar_tac) (by scalar_tac) s2 m2
        (by change leftCell left (AspisR1PoseidonPreparedIndexProductBounds.uFin i) 2#usize 2#usize _ _ _ = _; exact l22)
        (by change tableCell (tables i) 2#usize 2#usize _ _ = _; exact r22)
      _ = _ := by rw [hleftTotal, hrightTotal]
  exact ⟨hp00,hp01,hp02,hp10,hp11,hp12,hp20,hp21,hp22⟩

#print axioms product_cells
end AspisR1.PoseidonPreparedProductCells
