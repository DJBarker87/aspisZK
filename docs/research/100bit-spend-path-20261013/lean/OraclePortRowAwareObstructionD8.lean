import OraclePortRowAwareNoCollisionD6
import OracleDecisionDomSepFrozen

/-! Causality alone does not make terminal Merkle starts vanish.
This is a collision-free five-read prefix, not an accepted frozen proof. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortRowAwareObstructionD8
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OracleDecisionMultiDecoder OraclePortRowAwareWitnessD2
open OraclePortRowAwareGateWitnessD5 OraclePortRowAwareNoCollisionD6
open OraclePortRowAwareRecognizedD4 OraclePortRowAwareCausalD1
open DecodedFirstReadUnionBound
attribute [local irreducible] support initial row0 advanced squeezed node
attribute [local instance] Classical.propDecidable

theorem fold_cached {I A : Type} [DecidableEq I] (U T : Table I A)
    (tr : List (I × A)) (h : ∀ q ∈ tr, U q.1 = some q.2) (a : I) :
    applyTrace T tr a = if a ∈ tr.map Prod.fst then U a else T a := by
  induction tr generalizing T with
  | nil => simp [applyTrace]
  | cons q rest ih =>
    rw [applyTrace,ih (put T q.1 q.2) (fun r hr => h r (List.mem_cons_of_mem _ hr))]
    by_cases hr : a ∈ rest.map Prod.fst
    · simp [hr]
    · by_cases ha : a = q.1
      · subst a
        simp [hr,h q List.mem_cons_self,put]
      · simp [hr,ha,put]

theorem cached_table : applyTrace emptyTable past = support := by
  funext a
  rw [fold_cached support emptyTable past support_cached]
  split
  · rfl
  · rename_i hn
    have h0 : a ≠ initial.toBytes := by
      intro he; apply hn; rw [he]; exact List.mem_cons_self
    have h1 : a ≠ row0.toBytes := by
      intro he; apply hn; rw [he]; exact List.mem_cons_of_mem _ List.mem_cons_self
    have hs : a ≠ squeezed := by
      intro he; apply hn; rw [he]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have h2 : a ≠ advanced.toBytes := by
      intro he; apply hn; rw [he]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    simp only [emptyTable,support,if_neg h0,if_neg h1,if_neg h2,if_neg hs]

theorem node_fresh : support node = none := by
  have hl := byte_lengths
  have hs : squeezed.length = 33 := by
    simp [squeezed,squeezeA,Addr.toBytes_ofBytes,squeeze,bytes_length]
  have h0 : node ≠ initial.toBytes := by intro h; have := congrArg List.length h; omega
  have h1 : node ≠ row0.toBytes := by intro h; have := congrArg List.length h; omega
  have h2 : node ≠ advanced.toBytes := by intro h; have := congrArg List.length h; omega
  have h3 : node ≠ squeezed := by intro h; have := congrArg List.length h; omega
  simp only [support,if_neg h0,if_neg h1,if_neg h2,if_neg h3]

theorem rowaware_recognized (D : LiteralByteProtocol.Decoder) : decode D node support ≠ none := by
  rw [decode_of_gate D node support (gate_node D)]
  exact support_recognized

theorem terminal_start (D : LiteralByteProtocol.Decoder) :
    decoderFirstReads (decode D) support [(node,fun _ => 6)] = 1 := by
  simp only [decoderFirstReads,node_fresh,rowaware_recognized D,ne_eq,
    not_false_eq_true,and_self,if_true,Nat.add_zero]

/-- Fully instantiated same-prefix counterexample, for every Q. It rejects
"a node extending a recognised prefix implies collision". -/
theorem causal_node_without_collision (D : LiteralByteProtocol.Decoder) (Q : Nat) :
    applyTrace emptyTable past = support ∧
    Gate D node support ∧
    ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable (past ++ [(node,fun _ => 6)]) ∧
    decoderFirstReads (decode D) support [(node,fun _ => 6)] = 1 :=
  ⟨cached_table,gate_node D,clean_no_collision Q,terminal_start D⟩

theorem frozen_node : node = OracleDecisionDomSepFrozen.node
    (OracleDecisionMultiTree.children zero right) :=
by
  unfold node
  exact OracleDecisionDomSepFrozen.path_node_refines _

theorem no_universal_zero (D : LiteralByteProtocol.Decoder) :
    ¬ (∀ (cs : BinMerkle32Path.Children) (T : Table Bytes State),
      decode D (OracleDecisionDomSepFrozen.node cs) T = none) := by
  intro h
  apply rowaware_recognized D
  rw [frozen_node]
  exact h _ support

#print axioms fold_cached
#print axioms cached_table
#print axioms node_fresh
#print axioms rowaware_recognized
#print axioms terminal_start
#print axioms causal_node_without_collision
#print axioms frozen_node
#print axioms no_universal_zero
end AspisR1.OraclePortRowAwareObstructionD8
end
