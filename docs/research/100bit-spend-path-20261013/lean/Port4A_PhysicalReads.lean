import Port4A_ReaderInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4A_PhysicalReads
open Aeneas Aeneas.Std Result VTop_Stages
open CheckpointBytes5Effect
open AspisR1Stage2.WireTx2 (singletonParts checksumParts)

/-- Raw trace, requiring no canonicality, mathematical state, ROM law or
independent successful writer execution. -/
theorem writer_trace {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (proof pub : Slice U8) (saved : alloc.vec.Vec U8)
    (wrote : Port3_CheckpointInstall.writer D p a proof pub hash=ok saved) (before : Log) :
    ∃ hp hu hc,
      (VTop_Checkpoint.digest D).digest hash (singletonParts proof)=ok hp ∧
      (VTop_Checkpoint.digest D).digest hash (singletonParts pub)=ok hu ∧
      (VTop_Checkpoint.digest D).digest hash
        (checksumParts (CheckpointBytes5Writer.bodySlice
          (CheckpointBytes3Namespaces.toPrepared p) (CheckpointBytes3Namespaces.toAccumulator a) hp hu))=ok hc ∧
      VTop_Checkpoint.checkpointSlice saved=CheckpointBytes5Writer.finish
        (CheckpointBytes3Namespaces.toPrepared p) (CheckpointBytes3Namespaces.toAccumulator a) hp hu hc ∧
      run (VTop_Checkpoint.digest D) hash
        (CheckpointBytes5Writer.writer (CheckpointBytes3Namespaces.toPrepared p)
          (CheckpointBytes3Namespaces.toAccumulator a) proof pub) before =
        ok (VTop_Checkpoint.checkpointSlice saved,before ++
          [(singletonParts proof,hp),(singletonParts pub,hu),
           (checksumParts (CheckpointBytes5Writer.bodySlice
             (CheckpointBytes3Namespaces.toPrepared p) (CheckpointBytes3Namespaces.toAccumulator a) hp hu),hc)]) := by
  obtain ⟨after,success⟩ := Port3_CheckpointInstall.writer_run D p a proof pub hash saved wrote before
  have erased := run_success _ _ _ _ _ _ success
  simp only [CheckpointBytes5Writer.writer,erase_bind,erase_read,erase_pure] at erased
  obtain ⟨hp,hpCall,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ erased
  obtain ⟨hu,huCall,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ h
  obtain ⟨hc,hcCall,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ h
  have savedEq := (Result.ok.inj h).symm
  refine ⟨hp,hu,hc,hpCall,huCall,hcCall,savedEq,?_⟩
  rw [savedEq]
  simp only [CheckpointBytes5Writer.writer,run_bind,run_read,run_pure,hpCall,huCall,hcCall,
    bind_tc_ok,Aeneas.Std.uncurry,List.append_assoc,List.cons_append,List.nil_append]

/-- Six actual ordered reads with exactly the returned bytes passed to reader.
The returned p/a are the physical reader outputs. No S1S7S8 provenance premise
is needed to establish the read count/order or the same-byte Code composition. -/
theorem six_reads (base : Ops) (reserved : Bool) {H : Type}
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (wp : verifier.Prepared) (wa : verifier.Accumulator) (proof pub : Slice U8)
    (saved : alloc.vec.Vec U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (wrote : Port3_CheckpointInstall.writer D wp wa proof pub hash=ok saved)
    (resumed : (Port4A_ReaderInstall.install base reserved).op18 D
      (VTop_Checkpoint.checkpointSlice saved) proof pub .S2 hash=ok (.Ok (p,a)))
    (before : Log) :
    ∃ hp hu hc, ∃ c : AspisR1Stage2.Tx2ResumeDigests.Calls (VTop_Checkpoint.digest D) hash
      (VTop_Checkpoint.checkpointSlice saved) proof pub,
      run (VTop_Checkpoint.digest D) hash
        (CheckpointBytes5Join.stage reserved (CheckpointBytes3Namespaces.toPrepared wp)
          (CheckpointBytes3Namespaces.toAccumulator wa) proof pub) before =
        ok (.Ok (p,a),before ++
          [(singletonParts proof,hp),(singletonParts pub,hu),
           (checksumParts (CheckpointBytes5Writer.bodySlice
             (CheckpointBytes3Namespaces.toPrepared wp) (CheckpointBytes3Namespaces.toAccumulator wa) hp hu),hc),
           (c.proofParts,c.proofDigest),(c.publicParts,c.publicDigest),(c.checksumParts,c.checksumDigest)]) := by
  obtain ⟨hp,hu,hc,_,_,_,_,writerRun⟩ := writer_trace D hash wp wa proof pub saved wrote before
  have readerSource := Port4A_ReaderInstall.accepted_source base reserved D hash
    (VTop_Checkpoint.checkpointSlice saved) proof pub .S2 p a resumed
  obtain ⟨c,readerRun⟩ := CheckpointBytes5Trace.successful_log (CheckpointBytes4Ops.ops reserved)
    (VTop_Checkpoint.digest D) (fun s b h => CheckpointBytes4Comparison.ne_sound s b h)
    (VTop_Checkpoint.checkpointSlice saved) proof pub .S2 hash p a
    (before ++ [(singletonParts proof,hp),(singletonParts pub,hu),
      (checksumParts (CheckpointBytes5Writer.bodySlice
        (CheckpointBytes3Namespaces.toPrepared wp) (CheckpointBytes3Namespaces.toAccumulator wa) hp hu),hc)])
    readerSource
  refine ⟨hp,hu,hc,c,?_⟩
  simp only [CheckpointBytes5Join.stage,run_bind,writerRun,bind_tc_ok,Aeneas.Std.uncurry]
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using readerRun

#print axioms writer_trace
#print axioms six_reads
end AspisR1.Port4A_PhysicalReads
end
