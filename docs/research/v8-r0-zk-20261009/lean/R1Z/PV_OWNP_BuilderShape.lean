import R1Z.PV_OWNP_QueryStores
set_option autoImplicit false
namespace R1Z.PV_OWNP_BuilderShape
open Aeneas Aeneas.Std PV_OWNK_TowerCanon PV_OWNO_HelperArrays

theorem accepted_lengths (base : List (List U32))
 (h : PV_OWNO_Builder.acceptedBase base = true) :
 ∀ c ∈ base, c.length = 1024 := by
 intro c hc
 exact of_decide_eq_true ((Bool.and_eq_true_iff.mp ((List.all_eq_true.mp h) c hc)).1)

/-- The successful value projection has 29 columns of length1024. Failure of
any shape check, setup, helper, balance or finish continuation cannot produce
this successful result. No registry length is assumed. -/
theorem successful_lengths {E : Type} (publicError imbalance : E)
 (inverse : Q → Option Q) (base : Aeneas.Std.Array (List U32) 26#usize)
 (d g : Aeneas.Std.Array Q 1024#usize)
 (setup : Unit → Except E (Q × Q)) (registry : Q → Except E (List CopyRow))
 (balanced : List Q → Bool) (finish : List Q → Except E Unit) (out : List (List Q))
 (h : PV_OWNO_Builder.build publicError imbalance inverse base d g setup registry balanced finish = .ok out) :
 out.map List.length = List.replicate 29 1024 := by
 unfold PV_OWNO_Builder.build at h
 split at h
 · rename_i accepted
   have hb := accepted_lengths base.val (Bool.and_eq_true_iff.mp accepted).1
   cases hs : setup () with
   | error e => simp only [hs] at h; cases h
   | ok params =>
    rcases params with ⟨lambda,chi⟩
    simp only [hs] at h
    cases hr : PV_OWNO_HelperSelect.selected imbalance inverse chi (registry lambda) with
    | error e => simp only [hr] at h; cases h
    | ok h1 =>
     simp only [hr] at h
     split at h
     · cases h
     · rename_i hlen
       have hl : h1.length = 1024 := Classical.not_not.mp hlen
       split at h
       · cases hf : finish h1 with
         | error e => simp only [hf] at h; cases h
         | ok unit =>
          simp only [hf] at h
          cases Except.ok.inj h
          have hm : (base.val.map (List.map PV_OWNL_Inputs.lift)).map List.length =
            List.replicate 26 1024 := by
           rw [List.map_map]
           have he : base.val.map (fun c => (c.map PV_OWNL_Inputs.lift).length) =
             base.val.map (fun _ => 1024) := by
            apply List.map_congr_left
            intro c hc
            simpa only [List.length_map] using hb c hc
           rw [he,List.map_const]
           have bl := base.property
           change base.val.length = 26 at bl
           rw [bl]
          rw [List.map_append,hm]
          have dl := d.property
          have gl := g.property
          change d.val.length = 1024 at dl
          change g.val.length = 1024 at gl
          simp only [List.map_cons,List.map_nil,hl,dl,gl]
          rfl
       · cases h
 · cases h

/-- This theorem consumes the original builder success equation and the
bounded array-store execution. It remains a model theorem until the source
call's array/List and continuation associations are supplied. -/
theorem at_array_execution {E : Type} (publicError imbalance : E)
 (inverse : Q → Option Q) (base : Aeneas.Std.Array (List U32) 26#usize)
 (d g : Aeneas.Std.Array Q 1024#usize)
 (setup : Unit → Except E (Q × Q)) (registry : Q → Except E (List CopyRow))
 (balanced : List Q → Bool) (finish : List Q → Except E Unit) (columns : List (List Q))
 (built : PV_OWNO_Builder.build publicError imbalance inverse base d g setup registry balanced finish = .ok columns)
 (pub : PV_OWNM_V239.Public) (site : PV_OWNM_V239.Site)
 (combine : U64 → U32 → U64) (writes : List PV_OWNO_PointStores.Write) :
 PV_OWNM_V239.PV_OWNM_Link_ActualInput PV_OWNJ_Points.statement_points
  ⟨pub,site,(PV_OWNP_PointArray.run combine writes).val,columns⟩ ∧
 columns.map List.length = List.replicate 29 1024 := by
 constructor
 · rw [PV_OWNP_PointArray.run_view]
   exact PV_OWNO_PointStores.of_builder_execution publicError imbalance inverse base d g
    setup registry balanced finish columns built pub site combine writes
 · exact successful_lengths publicError imbalance inverse base d g setup registry balanced finish columns built

#print axioms accepted_lengths
#print axioms successful_lengths
#print axioms at_array_execution
end R1Z.PV_OWNP_BuilderShape
