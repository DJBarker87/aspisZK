import GeometryConcreteQueryValues
import R17QueryValuesSlotsStored
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1GeometryInputs.Proof
open alloc.vec R17CurrentM31Semantics

theorem inputTrace_nth (qv : QueryValues) (queries : Array U32 22#usize)
    {start end1 : Nat} {records : List InputRecord}
    (ht : InputTrace qv queries start end1 records) (k : Nat) (hk : k<records.length) :
    qv (queries.val.getD (start+k) 0#u32) = .ok (.Ok ((records[k]).1,(records[k]).2)) := by
  induction ht generalizing k with
  | nil n => simp at hk
  | cons i end1 values z tail hi hq ht ih =>
    cases k with
    | zero => simpa only [Nat.add_zero,List.getElem_cons_zero] using hq
    | succ k =>
      have hb : k<tail.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hk
      have hh := ih k hb
      simpa only [List.getElem_cons_succ,Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) : ∃ a, r=.ok a ∧ f a=.ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem concreteQueryValues_success_raw (q : U32) (values : Array M31 5#usize) (z : M31)
    (h : concreteQueryValues q = .ok (.Ok (values,z))) :
    R17QueryValuesWholeBodyV21.emittedRawWithCallees
      R17QueryValuesWholeBodyStoredV1.actualSourceCallees R17SliceAnySourceV1.queryZeroAny q =
      .ok (.Ok (values,z)) := by
  unfold concreteQueryValues at h
  rcases bind_ok_inv h with ⟨r,hr,h⟩
  cases r with
  | Err e => cases h
  | Ok x =>
    have he := core.result.Result.Ok.inj (Result.ok.inj h)
    subst x
    exact hr

private theorem map_getD {α β : Type} (xs : List α) (f : α → β) (i : Nat) (d : α) :
    (xs.map f).getD i (f d)=f (xs.getD i d) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,Option.getD_map]

theorem grouping_success_stored_inverse (queries : Array U32 22#usize)
    (start end1 : Usize) (inverse zs : Vec M31)
    (hrun : geometryAndInvert concreteQueryValues queries start end1 = .ok (.Ok (inverse,zs)))
    (i j : Usize) (hi : i.val<end1.val-start.val) (hj : j.val<5)
    (x : M31) (capture : AspisR1GeometryGrouping.geometry_groups.closure.closure)
    (hc : AspisR1GeometryGrouping.geometry_groups.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
      (inverse,i) j = .ok (x,capture)) :
    ∃ (u ix iy : AspisR1QueryGeometryActual.domain.FibreIndex)
      (hu : u.val<262144) (hix : ix.val<262144) (hiy : iy.val<262144),
      u.val=(queries.val.getD (start.val+i.val) 0#u32).val ∧
      ix.val=(u.val/4)*4 ∧ iy.val=(u.val/4)*4+3 ∧ capture=(inverse,i) ∧
      decode x =
        ([(R17TableCirclePowerBridge.circleCoords
            (AspisV7ExactOneFoldDomains.storedInitialFibrePoint20 ⟨u.val,hu⟩)).re,
          (R17TableCirclePowerBridge.circleCoords
            (AspisV7ExactOneFoldDomains.storedInitialFibrePoint20 ⟨u.val,hu⟩)).im,
          AspisV7ExactOneFoldDomains.storedFirstLineX18 ⟨ix.val,hix⟩,
          AspisV7ExactOneFoldDomains.storedFirstLineX18 ⟨iy.val,hiy⟩,
          2*(AspisV7ExactOneFoldDomains.storedFirstLineX18 ⟨ix.val,hix⟩)^2-1].getD j.val 0)⁻¹ := by
  obtain ⟨records,hri,ht,hcapture,hvalue⟩ :=
    concrete_grouping_success queries start end1 inverse zs hrun i j hi hj x capture hc
  have hq := inputTrace_nth concreteQueryValues queries ht i.val hri
  have hr := concreteQueryValues_success_raw _ _ _ hq
  obtain ⟨u,ix,iy,hu,hix,hiy,huq,hixv,hiyv,hslots,_⟩ :=
    R17QueryValuesSlotsStored.emitted_success_slot_values _ R17SliceAnySourceV1.queryZeroAny _ _ hr
  have hs := congrArg (fun a : List (ZMod P) => a.getD j.val 0) hslots
  have hm : ((records[i.val]).1.val.map decode).getD j.val 0 =
      decode ((records[i.val]).1.val.getD j.val 0#u32) :=
    map_getD (records[i.val]).1.val decode j.val 0#u32
  rw [hm] at hs
  exact ⟨u,ix,iy,hu,hix,hiy,huq,hixv,hiyv,hcapture,by rw [hvalue,hs]⟩


theorem grouping_success_canonical (queries : Array U32 22#usize)
    (start end1 : Usize) (inverse zs : Vec M31)
    (hrun : geometryAndInvert concreteQueryValues queries start end1 = .ok (.Ok (inverse,zs)))
    (i j : Usize) (hi : i.val<end1.val-start.val) (hj : j.val<5)
    (x : M31) (capture : AspisR1GeometryGrouping.geometry_groups.closure.closure)
    (hc : AspisR1GeometryGrouping.geometry_groups.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
      (inverse,i) j = .ok (x,capture)) : x.val<2147483647 := by
  obtain ⟨_,_,hcanonical,_,_,_,_,_,hinverseLen,_⟩ :=
    concrete_geometry_inverse_success queries start end1 inverse zs hrun
  have hb : 5*i.val+j.val < inverse.val.length := by omega
  have hx := AspisR1GeometryGrouping.Proof.grouping_callback_success inverse i j x capture hb hc
  apply hcanonical x
  rw [hx.2,List.getD_eq_getElem inverse.val 0#u32 hb]
  exact List.getElem_mem hb

#print axioms grouping_success_canonical

#print axioms inputTrace_nth
#print axioms concreteQueryValues_success_raw
#print axioms grouping_success_stored_inverse
end AspisR1GeometryInputs.Proof
