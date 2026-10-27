import R1Z.PrivacyR1FinalProtocolHistory

/-! Exact scan input dependencies and the operational prior-read event.
The finite ROM table is total; freshness refers to the read history, not
membership in its underlying finite address domain. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.QueryScanFreshInputs
open R0P R0Z R0Z.FsStatement R0Z.JointView R1Z.GamesR1 R1Z.GamesR1PBin
  R1Z.TranscriptR1 R1Z.LensR1 R1Z.LazyFrozen R1Z.CouplingR1PBin
  R1Z.AgreeR1PBin
attribute [local instance] Classical.propDecidable

/-- The state feeding each pair, in the actual answer-vector grammar. -/
def predecessor : Fin 8 → TRead
  | ⟨0, _⟩ => .absQ
  | ⟨n+1, hn⟩ => .qa ⟨n, by omega⟩

theorem scan_field (k : Fin 8) :
    fc (.qb k) = .ans (predecessor k) ∧
    fc (.qa k) = .ans (predecessor k) := by
  rcases k with ⟨_ | n, hk⟩ <;> exact ⟨rfl, rfl⟩

theorem scan_addresses (ρ : Rec) (k : Fin 8) :
    addr (.qb k) ρ = ans (ρ.tr (predecessor k)) ++ [1] ∧
    addr (.qa k) ρ = ans (ρ.tr (predecessor k)) ++ [2] := by
  obtain ⟨hb, ha⟩ := scan_field k
  simp only [addr, hb, ha, fieldVal, addrWith]
  exact ⟨trivial, trivial⟩

/-- Scan-specific prior reads of a causal program. The digest is the first
read; only earlier scheduled reads count. Post-proof adversary rereads do not. -/
def FreshFailure {m : ℕ} (scan : Fin m → Prop)
    (digest : List UInt8) (a : Fin m → (Fin m → OracleAnswer) → List UInt8)
    (H : List UInt8 → OracleAnswer) : Prop :=
  ∃ i, scan i ∧ (a i (runN a H 0 i.val) = digest ∨
    ∃ j : Fin m, j < i ∧
      a j (runN a H 0 j.val) = a i (runN a H 0 i.val))

theorem off_fresh_failure {m : ℕ} (scan : Fin m → Prop)
    (digest : List UInt8) (a : Fin m → (Fin m → OracleAnswer) → List UInt8)
    (H : List UInt8 → OracleAnswer) (hn : ¬ FreshFailure scan digest a H)
    (i : Fin m) (hi : scan i) :
    a i (runN a H 0 i.val) ≠ digest ∧
    ∀ j : Fin m, j < i →
      a j (runN a H 0 j.val) ≠ a i (runN a H 0 i.val) := by
  exact ⟨fun he => hn ⟨i, hi, Or.inl he⟩,
    fun j hj he => hn ⟨i, hi, Or.inr ⟨j, hj, he⟩⟩⟩

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- No salt, counter, prover secret or message appears directly in a scan
input. Entropy must be established for this preceding oracle answer. -/
theorem real_scan_addresses (W : R1Wire K CommitHandle Aux)
    (Pr : R1ProverP K CommitHandle Aux F W)
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : h.Instance) (sec : SecP)
    (d : OracleAnswer) (v : Pos1 Pr.E₁ Pr.E₂ → OracleAnswer) (k : Fin 8) :
    attAddr W Pr h B outputs x w sec d v (.inl (.qb k)) =
      ans (trOf v (predecessor k)) ++ [1] ∧
    attAddr W Pr h B outputs x w sec d v (.inl (.qa k)) =
      ans (trOf v (predecessor k)) ++ [2] := by
  exact scan_addresses _ k

#print axioms scan_field
#print axioms scan_addresses
#print axioms off_fresh_failure
#print axioms real_scan_addresses
end R1Z.QueryScanFreshInputs
