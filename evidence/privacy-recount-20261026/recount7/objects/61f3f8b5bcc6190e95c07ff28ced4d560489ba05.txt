import R1Z.PV_RunJoin_SliceTrace30
import R1Z.BuilderForestAdmissionPort
import R1Z.BuilderAdmissionCanonical
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SuperRootScan30
open Aeneas Aeneas.Std Result R0Z.WriterRefine BuilderStdModels
open BuilderForestStdPort BuilderForestAdmissionPort
open BuilderForestAdmissionPort.pool_v1
local instance (p : Prop) : Decidable p := Classical.propDecidable p
abbrev Roots := Array (Array U32 8#usize) 3#usize
abbrev outer := core.iter.traits.iterator.IteratorSliceIter (Array U32 8#usize)
abbrev conv := SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter U32 8#usize
abbrev inner := core.iter.traits.iterator.IteratorSliceIter U32
abbrev flat := core.iter.adapters.flatten.Flatten.Insts.CoreIterTraitsIteratorIterator outer conv inner
abbrev predicate := pair_forest_trace.compile_forest_from_copies.closure.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool

theorem trace (a : Roots) :
    FiniteTrace flat ⟨⟨Array.to_slice a,0⟩,none⟩ (a.val.flatMap (fun d => d.val)) := by
  change FiniteTrace (PV_RunJoin_FlattenTrace30.iterator outer conv inner) _ _
  apply PV_RunJoin_FlattenTrace30.flatten_trace outer conv inner (fun d => d.val)
  · intro d
    exact ⟨⟨Array.to_slice d,0⟩,rfl,PV_RunJoin_SliceTrace30.array_trace d⟩
  · exact PV_RunJoin_SliceTrace30.array_trace a
#print axioms trace

theorem roots_iff_list (a : Roots) :
    (∀ d ∈ a.val, Canon8 d) ↔ ∀ l, l<3 → Canon8 a.val[l]! := by
  constructor
  · intro h l hl
    have hlt : l<a.val.length := by simpa only [a.property,UScalar.ofNatCore_val_eq] using hl
    rw [getElem!_pos a.val l hlt]
    exact h _ (List.getElem_mem hlt)
  · intro h d hd
    obtain ⟨l,hl,he⟩ := List.mem_iff_getElem.mp hd
    have hlt : l<3 := by simpa only [a.property,UScalar.ofNatCore_val_eq] using hl
    simpa only [getElem!_pos a.val l hl,he] using h l hlt
#print axioms roots_iff_list

theorem scan_spec (a : Roots) :
    ∃ b after, core.iter.traits.iterator.Iterator.any.default flat predicate
      ⟨⟨Array.to_slice a,0⟩,none⟩ () = ok (b,after) ∧
      (b=false ↔ ∀ l, l<3 → Canon8 a.val[l]!) := by
  let g : U32 → Bool := fun x => decide (2147483647 ≤ x.val)
  have hf : ∀ (c : Unit) (x : U32), predicate.call_mut c x = ok (g x,c) := by
    intro c x
    change ok (decide (x≥aspis_core.field.P),c) = _
    simp only [g,UScalar.le_equiv,aspis_core.field.P,UScalar.ofNatCore_val_eq]
  obtain ⟨b,after,hr,hb⟩ := PV_RunJoin_IteratorAny30.any_trace flat predicate g hf
    ⟨⟨Array.to_slice a,0⟩,none⟩ _ (trace a) ()
  refine ⟨b,after,hr,hb.trans ?_⟩
  have hx : (∀ x ∈ a.val.flatMap (fun d => d.val), g x=false) ↔ ∀ d ∈ a.val, Canon8 d := by
    constructor
    · intro h d hd
      apply (BuilderAdmissionCanonical.canon_iff_list d).mpr
      intro x hx
      have hh := h x (List.mem_flatMap.mpr ⟨d,hd,hx⟩)
      simpa only [g,decide_eq_false_iff_not,not_le] using hh
    · intro h x hx
      obtain ⟨d,hd,hxd⟩ := List.mem_flatMap.mp hx
      have hh := (BuilderAdmissionCanonical.canon_iff_list d).mp (h d hd) x hxd
      simpa only [g,decide_eq_false_iff_not,not_le] using hh
  exact hx.trans (roots_iff_list a)
#print axioms scan_spec

theorem scan_false (a : Roots) (after : BuilderForestStd.Flatten _ _ _ _)
    (h : core.iter.traits.iterator.Iterator.any.default flat predicate
      ⟨⟨Array.to_slice a,0⟩,none⟩ () = ok (false,after)) :
    ∀ l, l<3 → Canon8 a.val[l]! := by
  obtain ⟨b,after',hr,hb⟩ := scan_spec a
  rw [h] at hr
  have he : b=false := (congrArg Prod.fst (Result.ok.inj hr)).symm
  exact hb.mp he
#print axioms scan_false
end R1Z.PV_RunJoin_SuperRootScan30
