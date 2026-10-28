import NDO_JFp_SHABlocks
set_option autoImplicit false
namespace AspisR1.JGz_HashTools
open JFp_SHA256

theorem length_flatten (cs : List (List Nat)) (lengths : ∀ b ∈ cs,b.length=64) :
    cs.flatten.length=64*cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hc := lengths c (List.mem_cons_self)
    have ht : ∀ b ∈ cs,b.length=64 := fun b hb=>lengths b (List.mem_cons_of_mem c hb)
    simp only [List.flatten_cons,List.length_append,hc,List.length_cons,ih ht]
    omega
#print axioms length_flatten

theorem hash_chunks (raw : List Nat) (cs : List (List Nat))
    (padded : pad raw=cs.flatten) (lengths : ∀ b ∈ cs,b.length=64) :
    JFp_SHA256.hash raw=cs.foldl (fun s b=>compress s (words b)) initial := by
  unfold JFp_SHA256.hash
  dsimp only
  rw [padded,length_flatten cs lengths]
  have divided : 64*cs.length/64=cs.length := by omega
  rw [divided,blocks_chunks cs lengths]
#print axioms hash_chunks
end AspisR1.JGz_HashTools
