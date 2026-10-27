# Exact remaining calls and joins

At JGr_Geometry.installed / JGr_Geometry.digest, retained proof/public buffers,
and SAME p/scratch/initial/pending/g returned by the checked preparation witness,
the local TX1 suffix is precisely one shared out/after/flushed/saved satisfying:

```lean
installed.op6 digest JFx_NativeBytes.proof p JGe_View.folded 0#usize ()=ok (.Ok ())
installed.op7 JFx_NativeBytes.proof p initial scratch none g pending 10#usize=ok (.Ok (out,after))
installed.op17 after out.weights.deref=ok flushed
installed.op16 digest p {out with weights:=⟨flushed.val,flushed.property⟩}
  JFx_NativeBytes.proof JFx_NativeBytes.publicInput ()=ok saved
saved.val=JFx_NativeBytes.checkpoint.val
```

The first call requires the actual native leaves, scratch and multiproof control
flow, in addition to the checked SHA/model-root arithmetic. The next call requires
query0..9's arithmetic gates and chained source accumulation. No suffix is
inferred merely because preparation/geometry exist. The final equality is about
the writer's RETURNED Vec, never a saved-byte field chosen independently.

No JGq_ source is merged in the starting tree. Inherited JGm_TX2_Batch.native
supplies batch1 in its stated dictionary, not accepted2. The actual TX2 suffix
still needs a common p/saved/g/geometry/pending/returned/after/flushed/back/v with:

```lean
Port4A_ReaderInstall.reader reserved D checkpoint proof pub .S2 hash=ok (.Ok (p,saved))
Port3_QueryStage.query (Port4C_RowStd.install (Port5Q1_QueryPorts.install queryOps))
  proof p saved g none geometry pending 22#usize=ok (.Ok (returned,after))
alloc.vec.Vec.deref_mut returned.weights=(returned.weights.deref,back)
Port3_FlushInstall.flush after returned.weights.deref=ok flushed
Port4D_FinishInstall.finish finish v p {returned with weights:=back flushed} none=ok (.Ok ())
```

Then derive both actual wrapper observations on this pair, the frozen3 SAME-pair
global join, and the game/RuntimePersistence/admission instantiation. Inherited
JFv_RuntimeWitness.compatible constructs a law-abiding runtime world for supplied
native functions, but does not prove those functions accept or share this actual
returned checkpoint. Current FJu finish-owner native/global terminal/mask
families and the external query budget remain as the ledger states. Deployment
observations remain included. JFm_Fixture.inhabited is not established.

The next exact batch consumer, after JGp_BatchInput.source normalises THIS
preparation, is:

```lean
Op5T_Install.body Port4B_Install.leaves
  (⟨JGn_TerminalIdentified.shaDictionary.coremarkerCopyInst,
    JGr_Geometry.digest.digest⟩ : AspisR1Stage2.aspis_core.digest.Digest32 Unit)
  JFx_NativeBytes.proof JFo_Prepared.value.queries JFo_Prepared.value.roots
  JGe_View.folded 0#usize () = ok (.Ok ())
```

This displayed source target is an OPEN equation, not a new theorem. The
concrete math-SHA hash adapter and the actual installed query dictionary must
be kept throughout. Neither successful model roots nor a value-only hash match
silently supplies the source verifier's state, branch path or ordered reads.
