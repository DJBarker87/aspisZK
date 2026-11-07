import NNH_ExceptOk
import NNH_Stage1Cut
set_option autoImplicit false
noncomputable section
namespace NNH_Tx1CallCut
open RSL NNH_Libraries NNH_ReturnedRE

structure Packet (a : TX1_094.Args VL) (saved : Bytes) (env : Env) where
 split : a.k=SPLIT
 parsed : LIB_VLib.parseShapeValue a.proof env=.ok ()
 scanned : LIB_VLib.canonicalScanValue a.proof env=.ok ()
 prepared : VL.Prepared × VL.E29
 prepare : NNH_Tx1Returns.preparedValue ⟨a.public_,a.proof,VL.zeroE29⟩ env=.ok prepared
 accumulator : VL.Acc
 accNew : LIB_VLib.accNewValue () env=.ok accumulator
 folded : B32
 folded_decode : TX1_136.toB32 (slice a.proof OFF_FOLDED_ROOT OFF_ROUND1)=some folded
 merkle : LIB_VLib.batchMerkleValue (a.proof,prepared.1,folded,0) env=.ok ()
 geometry : VL.Geo
 geometry_ok : LIB_VLib.geometryValue (prepared.1,0,a.k) env=.ok geometry
 pending : VL.Weights
 pending_ok : LIB_VLib.weightsNewValue accumulator env=.ok pending
 query : VL.Acc × VL.Weights
 query_ok : LIB_VLib.queryLoopValue (a.proof,prepared.1,accumulator,prepared.2,geometry,pending,a.k) env=.ok query
 saved_eq : LIB_VLib.checkpointValue (prepared.1,LIB_VLib.finishValue (query.2,query.1) env,a.proof,a.public_bytes) env=saved

theorem produce (a : TX1_094.Args VL) (saved : Bytes) (env : Env)
 (success : NNH_Tx1Returns.value a env=.ok saved) : Nonempty (Packet a saved env) := by
 unfold NNH_Tx1Returns.value at success
 obtain ⟨unit,guard,success⟩ := NNH_ExceptOk.bind _ _ saved success
 have split : a.k=SPLIT := by
  cases bad : (a.k != SPLIT) with
  | true => rw [bad] at guard; cases guard
  | false => exact bne_eq_false_iff_eq.mp bad
 obtain ⟨parsed,parse,success⟩ := NNH_ExceptOk.bind _ _ saved success
 cases parsed
 obtain ⟨scanned,scan,success⟩ := NNH_ExceptOk.bind _ _ saved success
 cases scanned
 obtain ⟨prepared,prepare,success⟩ := NNH_ExceptOk.bind _ _ saved success
 obtain ⟨accumulator,accNew,success⟩ := NNH_ExceptOk.bind _ _ saved success
 cases folded_run : TX1_136.toB32 (slice a.proof OFF_FOLDED_ROOT OFF_ROUND1) with
 | none => rw [folded_run] at success; cases success
 | some folded =>
  rw [folded_run] at success
  obtain ⟨merkle,merkle_ok,success⟩ := NNH_ExceptOk.bind _ _ saved success
  cases merkle
  obtain ⟨geometry,geometry_ok,success⟩ := NNH_ExceptOk.bind _ _ saved success
  obtain ⟨pending,pending_ok,success⟩ := NNH_ExceptOk.bind _ _ saved success
  obtain ⟨query,query_ok,success⟩ := NNH_ExceptOk.bind _ _ saved success
  obtain ⟨after,after_eq,success⟩ := NNH_ExceptOk.bind _ _ saved success
  have after_same := Except.ok.inj after_eq
  subst after
  obtain ⟨bytes,bytes_eq,success⟩ := NNH_ExceptOk.bind _ _ saved success
  have bytes_same := Except.ok.inj bytes_eq
  subst bytes
  exact ⟨⟨split,parse,scan,prepared,prepare,accumulator,accNew,folded,folded_run,merkle_ok,
   geometry,geometry_ok,pending,pending_ok,query,query_ok,Except.ok.inj success⟩⟩
#print axioms produce
end NNH_Tx1CallCut
