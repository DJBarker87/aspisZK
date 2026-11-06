import NLF_WrapperLaws
set_option autoImplicit false
namespace NLF_MetadataLaws
open NLF_RefCell NLF_SdkModel

theorem key_projection (s : State) (a : Nat) : unsigned_key s a=(s.accounts a).key := rfl
theorem owner_projection (s : State) (a : Nat) : owner s a=(s.accounts a).owner := rfl

theorem acquire_metadata (s : State) (i t : Nat) (k : Kind) :
    (wrap s i t k).1.accounts=s.accounts := wrapper_frame s i t k

theorem release_metadata (s : State) (g : Guard) (out : State) (h : release s g=.ok out) :
    out.accounts=s.accounts := by
  unfold release at h
  split at h
  · cases h
  · cases h; rfl

theorem release_payload (s : State) (g : Guard) (out : State) (h : release s g=.ok out) (i : Nat) :
    (out.cells i).payload=(s.cells i).payload := by
  cases hk : g.kind with
  | shared =>
    by_cases ok : (s.cells g.cell).writer=none ∧ g.token∈(s.cells g.cell).readers
    · have eq : release s g = .ok (put s g.cell {s.cells g.cell with readers:=(s.cells g.cell).readers.erase g.token}) := by
        simp [release,hk,dropShared,ok.1,ok.2]
      rw [eq] at h; cases h
      by_cases hi : i=g.cell <;> simp [put,hi]
    · simp [release,hk,dropShared,ok] at h
  | exclusive =>
    by_cases ok : (s.cells g.cell).writer=some g.token
    · have eq : release s g = .ok (put s g.cell {s.cells g.cell with writer:=none}) := by
        simp [release,hk,dropExclusive,ok]
      rw [eq] at h; cases h
      by_cases hi : i=g.cell <;> simp [put,hi]
    · simp [release,hk,dropExclusive,ok] at h

#print axioms key_projection
#print axioms owner_projection
#print axioms acquire_metadata
#print axioms release_metadata
#print axioms release_payload
end NLF_MetadataLaws
