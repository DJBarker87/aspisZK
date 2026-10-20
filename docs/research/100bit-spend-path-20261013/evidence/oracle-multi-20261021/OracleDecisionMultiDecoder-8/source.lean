import OracleDecisionMultiDecoderWalks

/-! A concrete decoder counterexample: a literal binary-node preimage can be
an ordinary row-one absorb address. The table is finite (three earlier
transcript cells, plus one leaf cell). No huge address universe is evaluated.
This refutes first-byte separation as a zero-start argument. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionMultiDecoder
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open CanonicalAddressEmbedding
open OracleDecisionMultiTree

theorem recognized_node : RecordedBinaryExperimentBin.dec node table ≠ none := by
  have habs : parseAbsorb nodeAddr = some (endpoint, p.lbl 1, p.enc m1) :=
    parseAbsorb_absorbA p endpoint (p.lbl 1) (p.enc m1) (p.encLen m1)
  have hc : CanonicalByteAddress.Canonical nodeAddr := by
    unfold nodeAddr absorbA; apply CanonicalByteAddress.canonical_ofBytes
  have hbytes : nodeAddr.toBytes = node := by
    simp only [nodeAddr, absorbA, Addr.toBytes_ofBytes, absorb]
    exact node_absorb.symm
  have hrow : UnifiedLabels.row (p.lbl 1) = 1 := by decide
  have hpub : RawFullPublicSelection.select node table = some pub := by
    rw [← hbytes]
    change RawPublicSelectionLift.select L (FullPublicSelection.select p)
      (toBytes (⟨nodeAddr, hc⟩ : AddrC L)) table = _
    rw [RawPublicSelectionLift.of_canonical]
    simp only [FullPublicSelection.select, habs, hrow]
    simp only [show 1 ≤ 26 from by decide, if_true, SemanticPublicSelection.select,
      walks.1, Option.map_some]
  have hctx : UnifiedSemanticContext.parse p pub.pubBytes nodeAddr
      (RawBoundedTrace.table L table) = some ⟨zero, records, m1⟩ := by
    apply UnifiedSemanticContext.parse_of_checks p _ _ _ endpoint _ _ zero records m1 habs
    · simp only [UnifiedSemanticRecovery.typed, walks.2, Option.bind_some,
        RawRoundDecode.decode_encode, Option.map_some]
    · exact IndexedMessage.read_encoded p 1 m1
  have hi : PublicInitParse.parse pub.pubBytes nodeAddr = none :=
    PublicInitAbsorbSeparation.parse_init_absorb_none p _ _ _ _ _
  rw [← hbytes]
  exact OracleDecisionMultiDecoderLift.semantic_recognizes pub ⟨nodeAddr,hc⟩ table
    endpoint (p.lbl 1) (p.enc m1) ⟨zero, records, m1⟩
    (by simpa only [toBytes, hbytes] using hpub) hi habs hrow hctx (by decide) (by decide)

theorem node_fresh : table node = none := by
  have h := byte_lengths
  have h0 : node ≠ initial.toBytes := by intro he; have := congrArg List.length he; omega
  have h1 : node ≠ row0.toBytes := by intro he; have := congrArg List.length he; omega
  have h2 : node ≠ advanced.toBytes := by intro he; have := congrArg List.length he; omega
  have h3 : node ≠ leaf := by intro he; have := congrArg List.length he; omega
  simp [table, h0, h1, h2, h3]

/-- Exactly one fresh recognized start on a single literal parent query. -/
theorem node_start_count (H : Bytes → State) :
    DecodedFirstReadUnionBound.decoderFirstReads RecordedBinaryExperimentBin.dec table
      (eval H (.ask node fun _ => (.done () : Program Bytes State Unit))).1 = 1 := by
  simp only [eval, DecodedFirstReadUnionBound.decoderFirstReads, node_fresh,
    recognized_node, ne_eq, not_false_eq_true, and_self, if_true, Nat.add_zero]

theorem leaf_cached : table leaf = some zero := by
  have h := byte_lengths
  have h0 : leaf ≠ initial.toBytes := by intro he; have := congrArg List.length he; omega
  have h1 : leaf ≠ row0.toBytes := by intro he; have := congrArg List.length he; omega
  have h2 : leaf ≠ advanced.toBytes := by intro he; have := congrArg List.length he; omega
  simp only [table, if_neg h0, if_neg h1, if_neg h2, ite_true]

def exampleTree : Tree := .branch (.opened leaf) (.supplied right)

theorem example_minimal : OracleDecisionMultiTree.Minimal exampleTree := by
  change True ∧ True ∧ 0 < 1 + 0
  decide

/-- An actual shared terminal, with a cached C2-width leaf and one supplied
sibling, contributes exactly one recognized fresh decoder start. -/
theorem terminal_start_count (H : Bytes → State) (hH : H leaf = zero) :
    DecodedFirstReadUnionBound.decoderFirstReads RecordedBinaryExperimentBin.dec table
      (eval H (terminal [⟨exampleTree,H node⟩] [] [])).1 = 1 := by
  simp only [terminal, OracleDecisionPrereqPaths.readFrames, List.nil_append,
    verifyTrees, exampleTree, execute, eval_bind, eval, hH,
    List.append_nil, List.nil_append, List.cons_append]
  change DecodedFirstReadUnionBound.decoderFirstReads RecordedBinaryExperimentBin.dec table
    [(leaf,zero),(node,H node)] = 1
  rw [DecodedFirstReadUnionBound.decoderFirstReads, FS.put_self table leaf zero leaf_cached]
  simp only [leaf_cached, reduceCtorEq, false_and, if_false, zero_add]
  exact node_start_count H

#print axioms leaf_cached
#print axioms example_minimal
#print axioms terminal_start_count
#print axioms recognized_node
#print axioms node_fresh
#print axioms node_start_count
end AspisR1.OracleDecisionMultiDecoder
end
