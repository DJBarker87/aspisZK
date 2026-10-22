import R1Z.ProverCommitCompact43
/-! Source compact-value loop using the verified native 32-byte cell and the
D157 pure chunks_exact observer. Visible failures are mapped to Semantic at
the shipped publication caller, exactly as in sim.rs. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitCompactSource46
open ProverCommitPublish43 (Bytes Error)
open ProverCommitCompact43
attribute [local instance] Classical.propDecidable

/-- Full fixed-width chunks, in order; any trailing incomplete bytes are
excluded. The default is unreachable for every enumerated cell index. -/
def chunks (xs : Bytes) : List Cell :=
  (List.range (xs.length/32)).map (fun k i => (xs[32*k+i.val]?).getD 0)

theorem chunk_bound (xs : Bytes) (k : Nat) (hk : k<xs.length/32) (i : Fin 32) :
    32*k+i.val<xs.length := by
  have bound := Nat.div_mul_le_self xs.length 32
  have hi := i.isLt
  omega

theorem chunks_length (xs : Bytes) : (chunks xs).length=xs.length/32 := by
  simp only [chunks,List.length_map,List.length_range]

structure API where
  chunks32 : Bytes → List Cell

/-- Pure slice::chunks_exact(32), with decoded fixed-width chunk slices.
This is an observer law, not a source codec or publication-success law. -/
structure TrustedChunks (api : API) : Prop where
  slice_chunks_exact32 : ∀ xs, api.chunks32 xs = chunks xs

def model : API := ⟨chunks⟩

def sourceValues (api : API) (xs out : Bytes) : Except Error Bytes :=
  if xs.length%32≠0 then .error .semantic else valuesLoop (api.chunks32 xs) out

def referenceValues (xs out : Bytes) : Except Error Bytes :=
  if xs.length%32≠0 then .error .semantic else values (chunks xs) out

theorem values_source (api : API) (std : TrustedChunks api) (xs out : Bytes) :
    sourceValues api xs out = referenceValues xs out := by
  simp only [sourceValues,referenceValues,std.slice_chunks_exact32,values_loop]

theorem values_reject_length (api : API) (xs out : Bytes) (bad : xs.length%32≠0) :
    sourceValues api xs out = .error .semantic := by
  unfold sourceValues
  exact if_pos bad

theorem values_success (api : API) (std : TrustedChunks api) (xs out result : Bytes) :
    sourceValues api xs out = .ok result ↔
      xs.length%32=0 ∧ (∀ c∈chunks xs, highZero c) ∧
        result=out ++ ((chunks xs).map low).flatten := by
  rw [values_source api std]
  unfold referenceValues
  by_cases length : xs.length%32=0
  · simp only [length,ne_eq,not_true_eq_false,if_false,true_and,values_ok]
  · simp only [length,ne_eq,not_false_eq_true,if_true,false_and]
    constructor <;> intro h <;> cases h

theorem values_length (api : API) (std : TrustedChunks api) (xs out result : Bytes)
    (ok : sourceValues api xs out = .ok result) :
    result.length=out.length+16*(xs.length/32) := by
  have h := (values_success api std xs out result).mp ok
  have exact : values (chunks xs) out = .ok result := (values_ok _ _ _).mpr h.2
  simpa only [chunks_length] using ProverCommitCompact43.values_length _ _ _ exact

theorem model_consistent : TrustedChunks model := ⟨fun _ => rfl⟩

#print axioms chunk_bound
#print axioms chunks_length
#print axioms values_source
#print axioms values_reject_length
#print axioms values_success
#print axioms values_length
#print axioms model_consistent
end R1Z.ProverCommitCompactSource46
