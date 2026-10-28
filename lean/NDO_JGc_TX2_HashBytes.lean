import NDO_JFp_SHADigest
set_option autoImplicit false
namespace AspisR1.JGc_TX2_HashBytes
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def bytes (xs : List Nat) : Bytes := xs.map (fun n => ⟨n%256,Nat.mod_lt _ (by omega)⟩)

def state (xs : List Nat) : State := fun i => ⟨xs.getD i.val 0 %256,Nat.mod_lt _ (by omega)⟩

theorem numeric (xs : List Nat) (canonical : ∀ n∈xs,n<256) :
    (bytes xs).map Fin.val=xs := by
  revert canonical
  induction xs with
  | nil => intro _;rfl
  | cons x xs ih =>
    intro canonical
    change x%256 :: (bytes xs).map Fin.val=x::xs
    rw [Nat.mod_eq_of_lt (canonical x (by simp)),ih (fun n hn => canonical n (by simp [hn]))]
#print axioms numeric
end AspisR1.JGc_TX2_HashBytes
