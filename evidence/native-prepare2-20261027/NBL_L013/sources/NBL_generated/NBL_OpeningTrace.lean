import NBL_BlockTrace
import NBL_PrepareControl
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBL_OpeningTrace
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NBL_PrepareControl NBL_BlockTrace

/-- One source-order S2 opening. Every succeeding call consumes the actual
preceding returned carrier, including root||round1 and serialized inactive.
There is no complete opening/prepare output equation in this record. -/
structure Trace {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H) where
  variant : v.variant=.S2
  seed : Bytes32
  seedCall : D.digest hash (NBA_Transcript.seedParts sem.transcript.state)=ok seed
  gamma : Scalar D (⟨seed,hash⟩ : transcript.Transcript H) 27#u8 v.y1 true
  inactiveBytes : Bytes32
  serialize : NBA_Installed.actual.sampling.toBytes v.inactive=ok inactiveBytes
  kappa : Scalar D gamma.block.after 28#u8 (Array.to_slice inactiveBytes) false
  alpha0 : Scalar D kappa.block.after 29#u8 v.round0 false
  root : Bytes32
  rootCall : v.folded_root=some root
  bytes1 bytes2 : alloc.vec.Vec U8
  appendRoot : alloc.vec.Vec.extend_from_slice core.clone.CloneU8
    (alloc.vec.Vec.with_capacity U8 256#usize) (Array.to_slice root)=ok bytes1
  appendRound : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 bytes1 v.round1=ok bytes2
  alpha1 : Scalar D alpha0.block.after 30#u8 (alloc.vec.Vec.deref bytes2) false

def Trace.output {H : Type} {D : aspis_core.Digest32 H}
    {sem : r1_semantic.Verified H} {v : verifier.View} {hash : H}
    (t : Trace D sem v hash) : Opening H :=
  ⟨t.gamma.value,t.kappa.value,Array.make 2#usize [t.alpha0.value,t.alpha1.value],
    t.alpha1.block.after,31#u8⟩

def Trace.log {H : Type} {D : aspis_core.Digest32 H}
    {sem : r1_semantic.Verified H} {v : verifier.View} {hash : H}
    (t : Trace D sem v hash) : Log :=
  [(NBA_Transcript.seedParts sem.transcript.state,t.seed)] ++ t.gamma.block.log ++
    t.kappa.block.log ++ t.alpha0.block.log ++ t.alpha1.block.log

theorem source {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (t : Trace D sem v hash) : opening NBA_Installed.actual D sem v hash=ok t.output := by
  have seed : transcript.Transcript.new D hash sem.transcript.state v.variant=
      ok (⟨t.seed,hash⟩ : transcript.Transcript H) := by
    rw [t.variant]
    exact NBA_Transcript.seed D hash sem.transcript.state t.seed t.seedCall
  have folds : transport.Variant.folds v.variant=ok 2#usize := by rw [t.variant]; rfl
  have capacity : (32#usize+224#usize : Result Usize)=ok 256#usize := by decide
  have root : core.option.Option.unwrap v.folded_root=ok t.root := by rw [t.rootCall]; rfl
  unfold opening
  simp only [r1_wire.SemanticTranscript.impl.state,seed,bind_tc_ok,
    scalar_result D _ _ _ _ t.gamma,t.serialize,lift,
    scalar_result D _ _ _ _ t.kappa,scalar_result D _ _ _ _ t.alpha0,
    folds,↓reduceIte,capacity,root,t.appendRoot,t.appendRound,
    scalar_result D _ _ _ _ t.alpha1,Trace.output]

/-- All thirteen chronological replies are constrained by the SAME digest
instance. No query suffix is included or erased by this opening trace. -/
theorem log_length {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (t : Trace D sem v hash) : t.log.length=13 := rfl

#print axioms source
#print axioms log_length
end AspisR1.NBL_OpeningTrace
end
