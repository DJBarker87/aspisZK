import GeometryGroupingIndex
import GeometryGroupingSlots
import GeometryInputsInverseComposition
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1GeometryInputs.Proof
open alloc.vec R17CurrentM31Semantics
private theorem map_getD {α β : Type} (xs : List α) (f : α → β) (i : Nat) (d : α) :
    (xs.map f).getD i (f d) = f (xs.getD i d) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,Option.getD_map]

theorem grouping_success_individual_inverse
    (qv : QueryValues) (queries : Array U32 22#usize) (hnz : NonzeroOutputs qv)
    (start end1 : Usize) (inverse zs : Vec M31)
    (hrun : geometryAndInvert qv queries start end1 = .ok (.Ok (inverse,zs)))
    (i j : Usize) (hi : i.val < end1.val-start.val) (hj : j.val < 5)
    (x : M31) (capture : AspisR1GeometryGrouping.geometry_groups.closure.closure)
    (hcallback : AspisR1GeometryGrouping.geometry_groups.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
      (inverse,i) j = .ok (x,capture)) :
    ∃ (records : List InputRecord) (hri : i.val<records.length),
      InputTrace qv queries start.val end1.val records ∧
      capture=(inverse,i) ∧
      decode x = (decode ((records[i.val]).1.val.getD j.val 0#u32))⁻¹ := by
  obtain ⟨_,_,_,records,ht,hinv,_,hlen,hinvlen,_⟩ :=
    geometryAndInvert_success qv queries hnz start end1 inverse zs hrun
  have hb : 5*i.val+j.val < inverse.val.length := by omega
  have hri : i.val<records.length := by omega
  obtain ⟨hc,hx⟩ := AspisR1GeometryGrouping.Proof.grouping_callback_success inverse i j x capture hb hcallback
  have hv := congrArg (fun xs : List (ZMod P) => xs.getD (5*i.val+j.val) 0) hinv
  have hleft : (inverse.val.map decode).getD (5*i.val+j.val) 0 =
      decode (inverse.val.getD (5*i.val+j.val) 0#u32) := by
    exact map_getD inverse.val decode (5*i.val+j.val) 0#u32
  have hright : (((records.flatMap (fun e => e.1.val)).map decode).map Inv.inv).getD (5*i.val+j.val) 0 =
      (decode ((records.flatMap (fun e => e.1.val)).getD (5*i.val+j.val) 0#u32))⁻¹ := by
    rw [show (0:ZMod P) = (0:ZMod P)⁻¹ from inv_zero.symm,
      map_getD ((records.flatMap (fun e => e.1.val)).map decode) Inv.inv (5*i.val+j.val) 0]
    exact congrArg Inv.inv (map_getD (records.flatMap (fun e => e.1.val)) decode (5*i.val+j.val) 0#u32)
  rw [hleft,hright,flat_slot records i.val j.val hri hj] at hv
  exact ⟨records,hri,ht,hc,by rw [hx]; exact hv⟩

#print axioms grouping_success_individual_inverse
end AspisR1GeometryInputs.Proof
