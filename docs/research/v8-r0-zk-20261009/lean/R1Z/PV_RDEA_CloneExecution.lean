import R1Z.PV_RDEA_StatefulPath
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEA_CloneExecution
open PV_RDB1_V183_ReserveWorld PV_RDEA_StatefulPath PV_RDEA_CapacityEndpoint

theorem capacity_success {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (address n : Nat) (w : World S F)
    (h : (PV_RDB1_V181.deployed step 18446744073709551615
      9223372036854775807 shape address n w).returned=.ok ()) :
    (PV_RDB1_V181.deployed step 18446744073709551615
      9223372036854775807 shape address n w).buffer.capacity=n := by
  unfold PV_RDB1_V181.deployed at h ⊢
  split at h <;> rename_i h1
  · cases h
  · simp only [h1,ite_false]
    split at h <;> rename_i h2
    · cases h
    · simp only [h2,ite_false]
      split at h <;> rename_i hz
      · simp only [hz,ite_true,PV_RDB1_V181.empty]
      · simp only [hz,ite_false]
        unfold finish at h ⊢
        dsimp only at h ⊢
        cases hs : step ⟨address,0,n,shape⟩ w.allocator with
        | mk p s => cases p <;> simp [PV_RDB1_V181.empty,hs] at h ⊢

/-- Unix to_path_buf/to_os_string/to_owned copies exactly the live bytes;
capacity is source length, rather than the source buffer's spare capacity. -/
def clone {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (address : Nat) (base : List U8) (w : World S F) :
    Outcome (Buffer U8) S F :=
  let e := PV_RDB1_V181.deployed step 18446744073709551615
    9223372036854775807 shape address base.length w
  match h : e.returned with
  | .error err => (.error err,e.world)
  | .ok () =>
    let b : Buffer U8 := ⟨e.buffer.address,e.buffer.capacity,base,by
      have hc := capacity_success step shape address base.length w h
      exact Nat.le_of_eq hc.symm⟩
    (.ok b,{e.world with memory := PV_RDB1_Append.writeTail e.buffer.address 0 base e.world.memory})

theorem clone_sizes {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (address : Nat)
    (base : List U8) (w : World S F) :
    sizes (clone step shape address base w).2.history =
      sizes w.history ++ requestSizes base.length := by
  unfold clone
  dsimp only
  split <;> exact all_sizes step shape width address base.length w

#print axioms capacity_success
#print axioms clone_sizes
end R1Z.PV_RDEA_CloneExecution
