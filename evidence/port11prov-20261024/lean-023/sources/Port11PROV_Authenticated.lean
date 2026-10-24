import Port11PROV_FirstBoth
import Port11PROV_Parser
import Port6AUTH_Recovery
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port11PROV_Authenticated
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.SqueezeOracleBridge
open MultiproofConeCanonical
open AspisV8R19.AdaptiveFirstReadLaw
theorem accepted (decoder : LiteralByteProtocol.Decoder) (adapter : AdapterRw.Ops)
    (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap) (rest : Implementation)
    {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X) (P : Port1_StoredCarrier.ByteProver) (H : Bytes → State)
    (std : Port1_Library.TrustedStd ops)
    (unwrap_ok : ∀ N b, unwrap N (.Ok b)=ok b)
    (occupied sibling : MultiproofConeP6Callbacks.Parent) (leaf : MultiproofConeP6Batch.Leaf)
    (binary : MultiproofConeP6Callbacks.Parent)
    (p6 : MultiproofConeP6Frozen2Stage.P6Boundary
      (Port4B_VerifyInstall.digest (VTop_Checkpoint.digest (Port9OR_Bodies.native D H)))
      hash H binary occupied sibling leaf)
    (sourceAccepted : (eval H (Port6AUTH_Prefix.source decoder
      (Port1_Driver.rust adapter (Port9OR_Installed.implementation ops reserved unwrap rest) D hash) P)).2.2=true) :
    let impl : Implementation := Port9OR_Installed.implementation ops reserved unwrap rest
    let rust := Port1_Driver.rust adapter impl D hash
    let input := (Port6AUTH_SourceCut.first rust P H).2.1
    ∃ pub proof semantic saved p a g folded p0 a0 g0 folded0 slice conversion zero variant written,
      Port1_Driver.asSlice input.statement.pubBytes=some pub ∧
      Port1_Driver.asSlice input.stored=some proof ∧ Port1_Driver.decodeSemantic adapter pub=ok (some semantic) ∧
      (eval H (interpret impl (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof 10#usize hash none))).2=ok (.Ok saved) ∧
      Port6CK_Reader.reader reserved unwrap (Port9OR_Bodies.native D H) saved.deref proof pub .S2 hash=ok (.Ok (p,a)) ∧
      a.next=10#usize ∧ (eval H (rest (.op17 29#usize p.gamma))).2=ok g ∧
      Port4B_Install.batch (Port9OR_Bodies.native D H) proof p folded 1#usize hash=ok (.Ok ()) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) proof
        {start:=7751#usize,«end»:=7783#usize}=ok slice ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 slice=ok conversion ∧
      ops.unwrap32 conversion=ok folded0 ∧
      Port4B_Install.batch (Port9OR_Bodies.native D H) proof p0 folded0 0#usize hash=ok (.Ok ()) ∧
      (eval H (interpret impl (Port10AUTH_TX1Cut.afterBatch D pub proof 10#usize hash none p0 a0 g0 (.Ok ())))).2=ok (.Ok saved) ∧
      (eval H (rest (.op3 proof))).2=ok (.Ok variant) ∧
      (eval H (rest (.op4 proof))).2=ok (.Ok ()) ∧
      (eval H (impl .op1)).2=ok zero ∧
      (eval H (rest (.op7 D semantic proof hash none (Array.repeat 29#usize zero)))).2=ok (.Ok p0,g0) ∧
      (eval H (rest (.op12 .S2))).2=ok (.Ok a0) ∧
      Port3_CheckpointInstall.writer (Port9OR_Bodies.native D H) p0 written proof pub hash=ok saved ∧
      p.queries=p0.queries ∧
      Port3_BatchStage.root0 p=Port3_BatchStage.root0 p0 ∧
      Port3_BatchStage.root1 p=Port3_BatchStage.root1 p0 ∧
      folded=folded0 ∧
      ∀ (parsed : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144),
        OraclePortCompactDraft.parse (bytesOf proof.val)=some parsed →
        Port4B_KeyInstall.queries p0.queries=q →
        Port3_BatchStage.root0 p0=encodeState (OraclePortBatchDraft.committedRoot parsed 0) →
        Port3_BatchStage.root1 p0=encodeState (OraclePortBatchDraft.committedRoot parsed 1) →
        ∀ Q, firstReads emptyTable (Port6AUTH_SourceCut.first rust P H).1 ≤ Q →
        ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
          BinRawByteCollisionTargets.pred Q) emptyTable (Port6AUTH_SourceCut.first rust P H).1 →
        ∀ (kind : Fin 3) (frame : Bytes) (selector : Fin 5),
        Read (Port6AUTH_SourceCut.first rust P H).1 frame →
        BinRawByteCollisionTargets.pred selector frame=some (OraclePortBatchDraft.committedRoot parsed kind.val) →
        ∀ pos, pos<22 →
        OraclePortAllSelectedRecoveryC6.recovered (Port6AUTH_SourceCut.first rust P H).1 frame parsed kind.val
          (OraclePortSelectedDraft.index q kind.val pos)=some (OraclePortPackedChoiceC4.payload parsed kind.val pos) := by
  let impl : Implementation := Port9OR_Installed.implementation ops reserved unwrap rest
  let rust := Port1_Driver.rust adapter impl D hash
  obtain ⟨pub,proof,semantic,saved,p,a,g,folded,p0,a0,g0,folded0,slice,conversion,zero,variant,written,
    hpub,hproof,decoded,tx1,resumed,next,powered,native1,range,copy,unwrapped,native0,suffix,parsedCall,checkedCall,zeroCall,preparedCall,initialCall,wrote,sameQueries,sameR0,sameR1,sameRoot,contains0,contains1⟩ :=
    Port11PROV_FirstBoth.accepted decoder adapter ops reserved unwrap rest D hash P H std unwrap_ok occupied sibling leaf
      p6.occupied_parent p6.sibling_parent p6.leaf sourceAccepted
  refine ⟨pub,proof,semantic,saved,p,a,g,folded,p0,a0,g0,folded0,slice,conversion,zero,variant,written,
    hpub,hproof,decoded,tx1,resumed,next,powered,native1,range,copy,unwrapped,native0,suffix,parsedCall,checkedCall,zeroCall,preparedCall,initialCall,wrote,sameQueries,sameR0,sameR1,sameRoot,?_⟩
  intro parsed q parseOK binding0 root00 root01 Q bound clean kind frame selector frameRead rootRead
  obtain ⟨len,wire⟩ := Port11PROV_Parser.length_wire proof parsed parseOK
  have binding1 : Port4B_KeyInstall.queries p.queries=q := by rw [sameQueries];exact binding0
  have root10 := sameR0.trans root00
  have root11 := sameR1.trans root01
  let nodes := Port11PROV_Views.nodes proof
  have views := Port11PROV_Views.node_bytes proof len parsed wire
  have root20 := Port11PROV_Views.folded ops std proof slice len parsed wire conversion folded0 range copy unwrapped
  have root21 := sameRoot.trans root20
  have source0 := Port10AUTH_Installed.accepted D hash H occupied sibling leaf p6.occupied_parent p6.sibling_parent p6.leaf
    proof len parsed wire p0 folded0 q binding0 0#usize (by decide) nodes views root00 root01 root20 native0
  have source1 := Port10AUTH_Installed.accepted D hash H occupied sibling leaf p6.occupied_parent p6.sibling_parent p6.leaf
    proof len parsed wire p folded q binding1 1#usize (by decide) nodes views root10 root11 root21 native1
  change eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed q nodes 0
    Port4B_BatchJoin.initial)=_ at source0
  change eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed q nodes 1
    Port4B_BatchJoin.initial)=_ at source1
  have frozen := MultiproofConeP6Frozen2Stage.both_batches
    (Port4B_VerifyInstall.digest (VTop_Checkpoint.digest (Port9OR_Bodies.native D H))) hash H
    binary occupied sibling leaf p6 parsed q nodes views
  have accepted0 : (eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed q nodes 0
      Port4B_BatchJoin.initial)).2=true := by rw [source0]
  have accepted1 : (eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed q nodes 1
      Port4B_BatchJoin.initial)).2=true := by rw [source1]
  have zero := (frozen.1 Port4B_BatchJoin.initial accepted0).symm.trans source0
  have one := (frozen.2 Port4B_BatchJoin.initial accepted1).symm.trans source1
  have consistent := FS.eval_consistent H
    (OraclePortRuntimeBindingC7.originalWith rust (OraclePortStoredAdmissionC4.canon (Port1_StoredCarrier.lift P)))
  apply Port6AUTH_Recovery.batches H (bytesOf proof.val) parsed parseOK q _ _
    (Port6AUTH_SourceCut.first rust P H).1 Q zero one
  · intro x hx
    apply contains0 parsed q len wire binding0 root00 root01 x
    change Read (eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed q nodes 0
      Port4B_BatchJoin.initial)).1 x
    rw [source0]
    exact hx
  · intro x hx
    apply contains1 parsed q len wire binding0 root00 root01 x
    change Read (eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed q nodes 1
      Port4B_BatchJoin.initial)).1 x
    rw [source1]
    exact hx
  · exact consistent
  · exact bound
  · exact clean
  · exact kind.isLt
  · exact frameRead
  · exact rootRead

#print axioms accepted
end AspisR1.Port11PROV_Authenticated
end
