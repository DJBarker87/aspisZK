import PV_B3P_HostPackSuccess227
import PV_B3P_PureBind227
import PV_B3P_P227_08
import PV_B3P_Offset226V3
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

/-- The exact guarded slice of one packed group; both tests bound the
subtraction before indexing. No assumption about field values is needed. -/
theorem window_total {N : Usize} (values : Array aspis_core.field.QM31 N)
    (start source : Usize) (hsum : start.val+N.val≤96) :
    Success (if source >= start then do
      let stop ← lift (Usize.wrapping_add start N)
      if source < stop then do
        let i ← lift (Usize.wrapping_sub source start)
        Array.index_usize values i
      else .ok aspis_core.field.QM31.ZERO
    else .ok aspis_core.field.QM31.ZERO) := by
  have hstop : (Usize.wrapping_add start N).val=start.val+N.val :=
    PV_B3P_Offset226V3.add_value start N (by
      have hsize := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac)
  by_cases hb : source >= start
  · simp only [hb,↓reduceIte,lift,bind_tc_ok]
    by_cases he : source < Usize.wrapping_add start N
    · simp only [he,↓reduceIte]
      apply index
      rw [PV_B3P_Offset226V3.sub_value source start (by scalar_tac)]
      scalar_tac
    · simp only [he,↓reduceIte]
      exact ok _
  · simp only [hb,↓reduceIte]
    exact ok _

#print axioms window_total

abbrev Packed24 := Array aspis_core.field.QM31 24#usize
abbrev PackedFlow := ControlFlow (Packed24 × Usize) Packed24

def PackedStep (j : Usize) (r : Result PackedFlow) : Prop :=
  ∃ next, r=.ok (.cont (next,j))

theorem step_bind {α : Type} (j : Usize) (r : Result α) (f : α → Result PackedFlow)
    (hr : Success r) (hf : ∀ x, PackedStep j (f x)) : PackedStep j (r >>= f) := by
  obtain ⟨x,hx⟩ := hr
  rw [hx]
  exact hf x

theorem step_lift {α : Type} (j : Usize) (x : α) (f : α → Result PackedFlow)
    (hf : PackedStep j (f x)) : PackedStep j (lift x >>= f) := hf

/-- The emitted do-notation uses join-point continuations for guarded reads.
This rule preserves that shape instead of expanding four windows into81 paths. -/
theorem step_window {N : Usize} (j : Usize) (values : Array aspis_core.field.QM31 N)
    (start source : Usize) (hsum : start.val+N.val≤96)
    (f : aspis_core.field.QM31 → Result PackedFlow) (hf : ∀ q, PackedStep j (f q)) :
    PackedStep j (if source >= start then do
      let stop ← lift (Usize.wrapping_add start N)
      if source < stop then do
        let i ← lift (Usize.wrapping_sub source start)
        let q ← Array.index_usize values i
        f q
      else f aspis_core.field.QM31.ZERO
    else f aspis_core.field.QM31.ZERO) := by
  have hstop : (Usize.wrapping_add start N).val=start.val+N.val :=
    PV_B3P_Offset226V3.add_value start N (by
      have hsize := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac)
  by_cases hb : source >= start
  · simp only [hb,↓reduceIte,lift,bind_tc_ok]
    by_cases he : source < Usize.wrapping_add start N
    · simp only [he,↓reduceIte]
      apply step_bind
      · apply index
        rw [PV_B3P_Offset226V3.sub_value source start (by scalar_tac)]
        scalar_tac
      exact hf
    · simp only [he,↓reduceIte]
      exact hf _
  · simp only [hb,↓reduceIte]
    exact hf _

#print axioms step_bind
#print axioms step_lift
#print axioms step_window

theorem preweighted_step {N : Usize} (packed : Array aspis_core.field.QM31 24#usize)
    (values : Array aspis_core.field.QM31 N) (start last i : Usize)
    (hsum : start.val+N.val≤96) (hlast : last.val<24) (hi : i≤last) :
    ∃ next, reference_terminal.add_preweighted_loop.body start values last packed i =
      .ok (.cont (next,Usize.wrapping_add i 1#usize)) := by
  change PackedStep (Usize.wrapping_add i 1#usize) _
  unfold reference_terminal.add_preweighted_loop.body
  rw [if_pos hi]
  apply step_lift
  apply step_lift
  apply step_lift
  apply step_window
  · exact hsum
  intro q0
  apply step_bind
  · apply update <;> scalar_tac
  intro w0
  apply step_lift
  apply step_lift
  apply step_window
  · exact hsum
  intro q1
  apply step_bind
  · apply update <;> scalar_tac
  intro w1
  apply step_lift
  apply step_lift
  apply step_window
  · exact hsum
  intro q2
  apply step_bind
  · apply update <;> scalar_tac
  intro w2
  apply step_lift
  apply step_lift
  apply step_window
  · exact hsum
  intro q3
  apply step_bind
  · apply update <;> scalar_tac
  intro w3
  apply step_bind
  · apply index <;> scalar_tac
  intro old
  apply step_lift
  apply step_bind
  · apply total_host_terminal_field_qm31_pack_base4
    simp only [Slice.len,Array.to_slice,w3.property]
    scalar_tac
  intro group
  apply step_bind
  · exact qadd old group
  intro value
  apply step_bind
  · apply update <;> scalar_tac
  intro next
  exact ⟨next,rfl⟩

#print axioms preweighted_step

theorem preweighted_loop_total {N : Usize} (packed : Array aspis_core.field.QM31 24#usize)
    (start : Usize) (values : Array aspis_core.field.QM31 N) (last i : Usize)
    (hsum : start.val+N.val≤96) (hlast : last.val<24) (hi : i.val≤last.val+1) :
    Success (reference_terminal.add_preweighted_loop packed start values last i) := by
  unfold reference_terminal.add_preweighted_loop
  refine loop_total _ (fun x : Array aspis_core.field.QM31 24#usize × Usize => last.val+1-x.2.val)
    (fun x => x.2.val≤last.val+1) ?_ (packed,i) hi
  rintro ⟨packed,i⟩ hi
  change i.val≤last.val+1 at hi
  by_cases hb : i≤last
  · obtain ⟨next,hnext⟩ := preweighted_step packed values start last i hsum hlast hb
    let j := Usize.wrapping_add i 1#usize
    have hj : j.val=i.val+1 := PV_B3P_Offset226V3.add_value i 1#usize (by
      have hsize := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac)
    refine ⟨.cont (next,j),hnext,?_,?_⟩
    · change j.val≤last.val+1
      scalar_tac
    · change last.val+1-j.val<last.val+1-i.val
      scalar_tac
  · refine ⟨.done packed,?_,True.intro⟩
    simp only [reference_terminal.add_preweighted_loop.body,hb,↓reduceIte]

#print axioms preweighted_loop_total

theorem preweighted_total {N : Usize} (packed : Array aspis_core.field.QM31 24#usize)
    (start : Usize) (values : Array aspis_core.field.QM31 N)
    (hpositive : 0<N.val) (hsum : start.val+N.val≤96) :
    Success (reference_terminal.add_preweighted packed start values) := by
  obtain ⟨first,hfirst,hfirstval⟩ := UScalar.div_spec (x:=start) (y:=4#usize) (by scalar_tac)
  let stop := Usize.wrapping_add start N
  have hstop : stop.val=start.val+N.val := PV_B3P_Offset226V3.add_value start N (by
    have hsize := Usize.cMax_bound_concrete.1
    rw [UScalar.size_def]
    scalar_tac)
  let finish := Usize.wrapping_sub stop 1#usize
  have hfinish : finish.val=stop.val-1 := PV_B3P_Offset226V3.sub_value stop 1#usize (by scalar_tac)
  obtain ⟨last,hlast,hlastval⟩ := UScalar.div_spec (x:=finish) (y:=4#usize) (by scalar_tac)
  unfold reference_terminal.add_preweighted
  rw [hfirst]
  simp only [lift,bind_tc_ok]
  simp only [finish,stop] at hlast
  rw [hlast]
  apply preweighted_loop_total _ _ _ _ _ hsum
  · change last.val<24
    have hf : finish.val<96 := by omega
    scalar_tac
  · have hle : start.val≤finish.val := by omega
    have hdiv : start.val/4 ≤ finish.val/4 := Nat.div_le_div_right hle
    scalar_tac

#print axioms preweighted_total
end PV_B3P_Success227
