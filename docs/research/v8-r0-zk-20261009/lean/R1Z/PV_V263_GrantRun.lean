import R1Z.PV_V263_GrantTeam
/-! Success of the complete revised candidate under primitive resource grants.
The only remaining hypothesis is the reached-index callback law. It is not
proved here for the deployed closures, and is not added at the endpoint. -/
set_option autoImplicit false
local instance {S : Type} : Monad (R1Z.PV_V263_World.Q S) where
  pure a := R1Z.PV_V263_World.lift (.ok a)
  bind := R1Z.PV_V263_World.bind
namespace R1Z.PV_V263_GrantRun
open Aeneas Aeneas.Std PV_V263_World PV_V263_WorkerRequests PV_V263_WorkerControl
open PV_V263_GrantControl PV_V263_GrantItems PV_V263_GrantTeam
open PV_RJ4IDB (Bytes)
variable {S A : Type}
variable (osCodec : {B : Type} → Request B → Bytes)
variable (vecCodec : PV_V263_MapSpine.VecCall → Bytes)
variable (layouts : PV_V263_MapSpine.Layouts) (n : Nat) (callback : Nat → Q S A)

theorem nested_total (law : CallbackLaw n callback) :
    Total (PV_V263_World.bind
      ((resourceWorld (S := S) osCodec vecCodec).vector (.collect 4 0 16 layouts.family))
      (fun _ => PV_V263_WorkerControl.traverse (fun k =>
        PV_V263_World.bind (PV_V263_SourceSpine.items (resourceWorld (S := S) osCodec vecCodec) layouts n k callback)
          (fun values => lift (.ok (values,values.length)))) (List.range 16))) := by
  apply bind_total _ _ (vector_total osCodec vecCodec _)
  intro unit w
  obtain ⟨values,h⟩ := PV_V263_Family.traverse_total_on _ (List.range 16) (fun k hk => by
    have bound : k < 16 := by simpa only [List.mem_range] using hk
    have total : Total (PV_V263_World.bind
        (PV_V263_SourceSpine.items (resourceWorld (S := S) osCodec vecCodec) layouts n k callback)
        (fun values => lift (.ok (values,values.length)))) := by
      apply bind_total _ _ (items_total osCodec vecCodec layouts n callback k bound law)
      intro values
      exact pure_returns _ (values,values.length) trivial
    intro v
    obtain ⟨a,ha,_⟩ := total v
    exact ⟨a,ha⟩) w
  exact ⟨values,h,trivial⟩

theorem nonnested_total (law : CallbackLaw n callback) :
    Total (withActive (grants osCodec) .abort 0 (do
      (resourceWorld (S := S) osCodec vecCodec).vector (.empty 2 0 layouts.handle)
      let handles ← PV_V263_SourceSpine.forks (resourceWorld (S := S) osCodec vecCodec) layouts n callback
      let first ← PV_V263_SourceSpine.caughtFamily (resourceWorld (S := S) osCodec vecCodec) layouts n 0 callback
      (resourceWorld (S := S) osCodec vecCodec).vector (.capacity 3 0 16 layouts.caught)
      (resourceWorld (S := S) osCodec vecCodec).vector (.push 3 0 0 layouts.caught)
      let others ← PV_V263_SourceSpine.joinChunks (resourceWorld (S := S) osCodec vecCodec) layouts 1 handles
      (resourceWorld (S := S) osCodec vecCodec).vector (.drop 2 0 layouts.handle)
      (grants osCodec).answer (.cleanup 0)
      (resourceWorld (S := S) osCodec vecCodec).vector (.capacity 4 0 16 layouts.family)
      let values ← PV_V263_SourceSpine.mergePool (resourceWorld (S := S) osCodec vecCodec) layouts 0 (first::others)
      (resourceWorld (S := S) osCodec vecCodec).vector (.drop 3 0 layouts.caught)
      pure values)) := by
  apply active_returns
  apply bind_total _ _ (vector_total osCodec vecCodec _)
  intro unit
  apply bind_returns _ _ _ _ (forks_good osCodec vecCodec layouts n callback law)
  intro handles hh
  apply bind_returns IsOk _ _ _ (caught_family osCodec vecCodec layouts n callback 0 (by decide) law)
  intro first hf
  apply bind_total _ _ (vector_total osCodec vecCodec _)
  intro unit
  apply bind_total _ _ (vector_total osCodec vecCodec _)
  intro unit
  apply bind_returns _ _ _ _ (join_chunks_good osCodec vecCodec layouts 1 handles hh)
  intro others ho
  apply bind_total _ _ (vector_total osCodec vecCodec _)
  intro unit
  apply bind_total _ _ (os_total osCodec _)
  intro unit
  apply bind_total _ _ (vector_total osCodec vecCodec _)
  intro unit
  have good : ∀ x, x ∈ first::others → IsOk x := by
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with hx | hx
    · subst x; exact hf
    · exact ho x hx
  apply bind_total _ _ (merge_total osCodec vecCodec layouts 0 (first::others) good)
  intro values
  apply bind_total _ _ (vector_total osCodec vecCodec _)
  intro unit
  exact pure_returns _ values trivial

theorem pool_total (law : CallbackLaw n callback) :
    Total (PV_V263_SourceSpine.pool (resourceWorld (S := S) osCodec vecCodec) layouts n callback) := by
  apply bind_total _ _ (os_total osCodec _)
  intro active
  cases active with
  | false => exact nonnested_total osCodec vecCodec layouts n callback law
  | true => exact nested_total osCodec vecCodec layouts n callback law

theorem run_total (stage : Nat) (law : CallbackLaw n callback) :
    Total (PV_V263_SourceSpine.run (resourceWorld (S := S) osCodec vecCodec) layouts stage n callback) := by
  apply bind_total _ _ (pool_total osCodec vecCodec layouts n callback law)
  intro chunks
  apply bind_total _ _ (vector_total osCodec vecCodec _)
  intro unit
  apply bind_total _ _ (append_total osCodec vecCodec layouts 0 0 chunks)
  intro values
  apply bind_total _ _ (vector_total osCodec vecCodec _)
  intro unit
  exact pure_returns _ values trivial

#print axioms nested_total
#print axioms nonnested_total
#print axioms pool_total
#print axioms run_total
end R1Z.PV_V263_GrantRun
