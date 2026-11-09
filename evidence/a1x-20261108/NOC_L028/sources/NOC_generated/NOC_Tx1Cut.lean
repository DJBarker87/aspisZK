import NNH_Tx1Returns
import NNH_ExceptOk
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOC_Tx1Cut
open RSL
abbrev V := NNH_Tx1Returns.V

/-- Canonical returned-path decomposition of the 094 library value, retaining
every SAME intermediate value. -/
structure Packet (a : TX1_094.Args V) (env : Env) (out : Bytes) where
 split : (a.k != SPLIT) = false
 parsed : LIB_VLib.parseShapeValue a.proof env = .ok ()
 scanned : LIB_VLib.canonicalScanValue a.proof env = .ok ()
 p : LIB_VCarriers.Prepared
 g : LIB_VCarriers.E29
 prepared : NNH_Tx1Returns.preparedValue ⟨a.public_,a.proof,V.zeroE29⟩ env = .ok (p,g)
 acc : LIB_VCarriers.Acc
 accOk : LIB_VLib.accNewValue () env = .ok acc
 folded : B32
 foldedOk : TX1_136.toB32 (slice a.proof OFF_FOLDED_ROOT OFF_ROUND1) = some folded
 batch : LIB_VLib.batchMerkleValue (a.proof,p,folded,0) env = .ok ()
 geo : LIB_VCarriers.Geo
 geoOk : LIB_VLib.geometryValue (p,0,a.k) env = .ok geo
 pending : LIB_VCarriers.Weights
 pendingOk : LIB_VLib.weightsNewValue acc env = .ok pending
 r : LIB_VCarriers.Acc × LIB_VCarriers.Weights
 rOk : LIB_VLib.queryLoopValue (a.proof,p,acc,g,geo,pending,a.k) env = .ok r
 out_eq : out = LIB_VLib.checkpointValue (p,LIB_VLib.finishValue (r.2,r.1) env,a.proof,a.public_bytes) env

theorem returned (a : TX1_094.Args V) (env : Env) (out : Bytes)
 (called : NNH_Tx1Returns.value a env = .ok out) : Nonempty (Packet a env out) := by
 unfold NNH_Tx1Returns.value at called
 obtain ⟨u,hu,called⟩ := NNH_ExceptOk.bind _ _ out called
 have split : (a.k != SPLIT) = false := by
  cases hk : (a.k != SPLIT)
  · rfl
  · rw [hk] at hu; cases hu
 obtain ⟨u1,hparse,called⟩ := NNH_ExceptOk.bind _ _ out called
 obtain ⟨u2,hscan,called⟩ := NNH_ExceptOk.bind _ _ out called
 obtain ⟨pg,hprep,called⟩ := NNH_ExceptOk.bind _ _ out called
 obtain ⟨acc,hacc,called⟩ := NNH_ExceptOk.bind _ _ out called
 cases hf : TX1_136.toB32 (slice a.proof OFF_FOLDED_ROOT OFF_ROUND1) with
 | none => rw [hf] at called; cases called
 | some folded =>
  rw [hf] at called
  obtain ⟨u3,hbatch,called⟩ := NNH_ExceptOk.bind _ _ out called
  obtain ⟨geo,hgeo,called⟩ := NNH_ExceptOk.bind _ _ out called
  obtain ⟨pending,hpend,called⟩ := NNH_ExceptOk.bind _ _ out called
  obtain ⟨r,hr,called⟩ := NNH_ExceptOk.bind _ _ out called
  obtain ⟨acc2,hacc2,called⟩ := NNH_ExceptOk.bind _ _ out called
  obtain ⟨bytes,hbytes,called⟩ := NNH_ExceptOk.bind _ _ out called
  cases u1; cases u2; cases u3
  have e1 := (Except.ok.inj hacc2).symm
  have e2 := (Except.ok.inj hbytes).symm
  have e3 := (Except.ok.inj called).symm
  subst e1; subst e2; subst e3
  exact ⟨⟨split,hparse,hscan,pg.1,pg.2,hprep,acc,hacc,folded,rfl,hbatch,geo,hgeo,pending,hpend,r,hr,rfl⟩⟩
#print axioms returned
end AspisR1.NOC_Tx1Cut
end
