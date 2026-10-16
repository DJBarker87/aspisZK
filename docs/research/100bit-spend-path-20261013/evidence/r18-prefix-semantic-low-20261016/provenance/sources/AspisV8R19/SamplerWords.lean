import AspisV8R19.SourceOraclePrograms

/-! Mathematical semantics of the source's eight little-endian u32 words.
Masking is literal bit-and, not an assumed uniform-candidate interface. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerWords
open DuplexFrames SourceDuplexStep

def word (block : State) (j : Fin 8) : Nat :=
  (block ⟨4*j.val,by omega⟩).val + 256*(block ⟨4*j.val+1,by omega⟩).val +
  65536*(block ⟨4*j.val+2,by omega⟩).val + 16777216*(block ⟨4*j.val+3,by omega⟩).val

theorem word_bound (block : State) (j : Fin 8) : word block j < 4294967296 := by
  have h0 := (block ⟨4*j.val,by omega⟩).isLt
  have h1 := (block ⟨4*j.val+1,by omega⟩).isLt
  have h2 := (block ⟨4*j.val+2,by omega⟩).isLt
  have h3 := (block ⟨4*j.val+3,by omega⟩).isLt
  unfold word
  omega

def masked (bits : Nat) (w : Nat) : Nat := w &&& (2^bits-1)

theorem masked_eq_mod (bits w : Nat) : masked bits w = w % 2^bits :=
  Nat.and_two_pow_sub_one_eq_mod w bits

theorem masked_bound (bits w : Nat) : masked bits w < 2^bits := by
  rw [masked_eq_mod]
  exact Nat.mod_lt _ (by positivity)

def words (bits : Nat) (block : State) : List Nat :=
  List.ofFn (fun j : Fin 8 => masked bits (word block j))

theorem words_length (bits : Nat) (block : State) : (words bits block).length = 8 := by
  simp [words]

theorem words_bounded (bits : Nat) (block : State) (w : Nat) (h : w ∈ words bits block) :
    w < 2^bits := by
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp h
  exact masked_bound bits _

theorem source31_mask (w : Nat) : masked 31 w = w &&& 2147483647 := rfl
theorem source18_mask (w : Nat) : masked 18 w = w &&& 262143 := rfl

#print axioms word_bound
#print axioms masked_eq_mod
#print axioms masked_bound
#print axioms words_length
#print axioms words_bounded
#print axioms source31_mask
#print axioms source18_mask
end AspisV8R19.SamplerWords
