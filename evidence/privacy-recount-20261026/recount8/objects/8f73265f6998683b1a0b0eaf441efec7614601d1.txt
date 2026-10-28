import R1Z.ProverCommitDigest26
/-! A precise limitation of the current extracted oracle interface.
This does not refute privacy: it prevents identifying the native cursor-based
CoinOracle with a stateless Digest32 instance without an effect transport. -/
set_option autoImplicit false
namespace R1Z.ProverCommitOracleEffect26
open Aeneas Aeneas.Std Result
abbrev Bytes32 := Array U8 32#usize
abbrev Parts := Slice (Slice U8)

def readStream (coins : List Bytes32) (cursor : Nat) (_ : Parts) : Bytes32 × Nat :=
  ((coins[cursor]?).getD (Array.repeat 32#usize 0#u8),cursor+1)

/-- Exact cursor behavior, including the ignored query input. -/
theorem two_reads (first second : Bytes32) (parts : Parts) :
    readStream [first,second] 0 parts = (first,1) ∧
    readStream [first,second] 1 parts = (second,2) := ⟨rfl,rfl⟩

/-- The current generated interface returns no updated handle or heap.
It cannot unconditionally realize two distinct answers at one input and
one retained handle. A freshness/effect transport is therefore necessary. -/
theorem no_stateless_interpretation {H : Type}
    (digest : AspisR1SimSemantic20.aspis_core.digest.Digest32 H)
    (handle : H) (parts : Parts) (first second : Bytes32) (different : first ≠ second) :
    ¬ (digest.digest handle parts = ok first ∧ digest.digest handle parts = ok second) := by
  rintro ⟨hfirst,hsecond⟩
  exact different (Result.ok.inj (hfirst.symm.trans hsecond))

#print axioms two_reads
#print axioms no_stateless_interpretation
end R1Z.ProverCommitOracleEffect26
