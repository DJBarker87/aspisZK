import R1Z.PV_RunJoin_QueryFillStep64
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryFillTotal64
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_FibreFillThread43 (Matrix phase)

theorem finite (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (c : host_commitment.Commitment)
    (domain : PV_RunJoin_QueryFillStep64.Domain c)
    (u : aspis_core.r0.domain.FibreIndex) (bound : u.val<262144)
    (n : Nat) (values : Matrix) (j : Usize) (rank : j.val+n=c.lanes.length) :
    ∃ next, @phase (types base) (selected base heap box ops) n c u values j=ok next := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  induction n generalizing values j with
  | zero => exact ⟨values,rfl⟩
  | succ n ih =>
    obtain ⟨middle,hm⟩ := PV_RunJoin_QueryFillStep64.total base heap box ops c domain
      u bound values j (by omega)
    have inc := PV_RunJoin_MergeLoop35.increment j (by have small := domain.1;omega)
    obtain ⟨next,hn⟩ := ih middle (Usize.wrapping_add j 1#usize) (by rw [inc];omega)
    exact ⟨next,by simp only [phase,hm,bind_tc_ok,hn]⟩

theorem values (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (c : host_commitment.Commitment)
    (domain : PV_RunJoin_QueryFillStep64.Domain c)
    (u : aspis_core.r0.domain.FibreIndex) (bound : u.val<262144) (initial : Matrix) :
    ∃ next, @host_commitment.fill_opening_values (types base) (selected base heap box ops)
      c u initial 0#usize=ok next := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  rw [PV_RunJoin_FibreFillThread43.thread c.lanes.length c u initial 0#usize (by rfl) domain.1]
  exact finite base heap box ops c domain u bound c.lanes.length initial 0#usize rfl

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (c : host_commitment.Commitment)
    (domain : PV_RunJoin_QueryFillStep64.Domain c)
    (u : aspis_core.r0.domain.FibreIndex) (bound : u.val<262144)
    (opening : aspis_core.r0.wire.FibreOpening) :
    ∃ next, @host_commitment.Commitment.fill_opening (types base) (selected base heap box ops)
      c u opening=ok next := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  obtain ⟨matrix,hm⟩ := values base heap box ops c domain u bound opening.values
  obtain ⟨path,hpath,hbound⟩ : ∃ path, host_commitment.opening_path c.time=ok path ∧ path.val<2 := by
    cases c.time <;> exact ⟨_,rfl,by decide⟩
  let zero := Array.repeat 32#usize 0#u8
  obtain ⟨paths,hpaths,hpost⟩ := WP.spec_imp_exists
    (Array.update_spec opening.paths path (Array.repeat 6#usize (Array.repeat 7#usize zero)) hbound)
  refine ⟨⟨matrix,paths⟩,?_⟩
  simp only [host_commitment.Commitment.fill_opening,hm,hpath,bind_tc_ok,hpaths]

#print axioms finite
#print axioms values
#print axioms complete
end R1Z.PV_RunJoin_QueryFillTotal64
