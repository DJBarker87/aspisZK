import R1Z.PV_RunJoin_SpendDataMap
import R1Z.PV_RunJoin_FixtureRecords
import R1Z.PV_RunJoin_NoteHashMap
import R1AppendPath

/-! Ring-hom naturality for the public append binding. This transports the
public append equations through an injective field map; it adds no statement
about how the public values were produced. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_AppendBindingMap
open AspisR1

open R0P AspisPool.V7PairLeafOccupancy SpendRelation
open R1Z.PV_RunJoin_PoseidonMap

variable {K L : Type} [Field K] [Field L] (f : K →+* L)

theorem digest_injective (hf : Function.Injective f) :
    Function.Injective (PV_RunJoin_SpendDataMap.digest f : R0P.Digest K → R0P.Digest L) := by
  intro x y h
  funext i
  exact hf (congrFun h i)

theorem digest_nodeCompress (a b : R0P.Digest K) :
    PV_RunJoin_SpendDataMap.digest f (nodeCompress a b) =
      nodeCompress (PV_RunJoin_SpendDataMap.digest f a) (PV_RunJoin_SpendDataMap.digest f b) := by
  change PV_RunJoin_PoseidonMap.mapDigest f (nodeCompress a b) =
    nodeCompress (PV_RunJoin_PoseidonMap.mapDigest f a) (PV_RunJoin_PoseidonMap.mapDigest f b)
  exact PV_RunJoin_PoseidonMap.map_nodeCompress f a b

theorem digest_zero :
    PV_RunJoin_SpendDataMap.digest f (fun _ : Fin 8 => (0 : K)) =
      (fun _ : Fin 8 => (0 : L)) := by
  funext i
  exact map_zero f

theorem map_frozenEmpty (level : Fin 21) :
    PV_RunJoin_SpendDataMap.digest f (AppendNode.frozenEmpty (K := K) level) =
      AppendNode.frozenEmpty (K := L) level := by
  funext i
  dsimp [PV_RunJoin_SpendDataMap.digest, AppendNode.frozenEmpty]
  exact map_natCast f _

theorem map_step (pub : Public K) (level : Fin 20) (cur : R0P.Digest K) :
    PV_RunJoin_SpendDataMap.digest f (AppendPath.step pub level cur) =
      AppendPath.step (PV_RunJoin_SpendDataMap.mapPublic f pub) level
        (PV_RunJoin_SpendDataMap.digest f cur) := by
  unfold AppendPath.step
  change
    PV_RunJoin_SpendDataMap.digest f
      (if digestBitZero pub level then
        nodeCompress cur (AppendNode.frozenEmpty level.castSucc)
       else
        nodeCompress (pub.snapshotFrontier level) cur) =
    (if digestBitZero pub level then
      nodeCompress (PV_RunJoin_SpendDataMap.digest f cur) (AppendNode.frozenEmpty level.castSucc)
     else
      nodeCompress (PV_RunJoin_SpendDataMap.digest f (pub.snapshotFrontier level))
        (PV_RunJoin_SpendDataMap.digest f cur))
  by_cases h : digestBitZero pub level
  · simp only [if_pos h]
    rw [digest_nodeCompress, map_frozenEmpty]
  · simp only [if_neg h]
    exact digest_nodeCompress f _ _

theorem map_pathPrefix (pub : Public K) (leaf : R0P.Digest K) (n : Nat) :
    PV_RunJoin_SpendDataMap.digest f (AppendPath.pathPrefix pub leaf n) =
      AppendPath.pathPrefix (PV_RunJoin_SpendDataMap.mapPublic f pub)
        (PV_RunJoin_SpendDataMap.digest f leaf) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      unfold AppendPath.pathPrefix
      by_cases hn : n < 20
      · simp only [dif_pos hn]
        rw [map_step, ih]
      · simp only [dif_neg hn]
        exact ih

theorem map_outputPair (pub : Public K) :
    outputPair (PV_RunJoin_SpendDataMap.mapPublic f pub) =
      (outputPair pub).map (PV_RunJoin_SpendDataMap.digest f) := by
  cases hv : pub.variant with
  | privateTransfer =>
      cases hr : pub.recipient <;>
        simp [outputPair, PV_RunJoin_SpendDataMap.mapPublic, hv, hr,
          digest_nodeCompress]
  | withdrawal =>
      simp [outputPair, PV_RunJoin_SpendDataMap.mapPublic, hv,
        digest_nodeCompress, digest_zero]

theorem appendBinding_map_iff (pub : Public K) :
    AppendBinding (PV_RunJoin_SpendDataMap.mapPublic f pub) ↔ AppendBinding pub := by
  have hf : Function.Injective f := f.injective
  have hd : Function.Injective (PV_RunJoin_SpendDataMap.digest f : R0P.Digest K → R0P.Digest L) :=
    digest_injective f hf
  constructor
  · rintro ⟨pairL, hpairL, hrootL, hcarryL⟩
    cases hpair : outputPair pub with
    | none =>
        rw [map_outputPair f pub, hpair] at hpairL
        cases hpairL
    | some pairK =>
        have hpairMapped :
            outputPair (PV_RunJoin_SpendDataMap.mapPublic f pub) =
              some (PV_RunJoin_SpendDataMap.digest f pairK) := by
          rw [map_outputPair f pub, hpair]
          rfl
        have hpairValue : pairL = PV_RunJoin_SpendDataMap.digest f pairK :=
          Option.some.inj (hpairL.symm.trans hpairMapped)
        refine ⟨pairK, hpair, ?_, ?_⟩
        · apply hd
          calc
            PV_RunJoin_SpendDataMap.digest f pub.nextRoot =
                (PV_RunJoin_SpendDataMap.mapPublic f pub).nextRoot := rfl
            _ = AppendPath.pathPrefix (PV_RunJoin_SpendDataMap.mapPublic f pub) pairL 20 := hrootL
            _ = AppendPath.pathPrefix (PV_RunJoin_SpendDataMap.mapPublic f pub)
                  (PV_RunJoin_SpendDataMap.digest f pairK) 20 := by rw [hpairValue]
            _ = PV_RunJoin_SpendDataMap.digest f (AppendPath.pathPrefix pub pairK 20) :=
                  (map_pathPrefix f pub pairK 20).symm
        · intro hc
          have hcMapped : digestCarry (PV_RunJoin_SpendDataMap.mapPublic f pub).nextPairIndex < 20 := by
            simpa [PV_RunJoin_SpendDataMap.mapPublic] using hc
          have hfrontier :
              PV_RunJoin_SpendDataMap.digest f
                (pub.nextFrontier ⟨digestCarry pub.nextPairIndex, hc⟩) =
              AppendPath.pathPrefix (PV_RunJoin_SpendDataMap.mapPublic f pub) pairL
                (digestCarry (PV_RunJoin_SpendDataMap.mapPublic f pub).nextPairIndex) := by
            simpa [PV_RunJoin_SpendDataMap.mapPublic] using hcarryL hcMapped
          apply hd
          calc
            PV_RunJoin_SpendDataMap.digest f
                (pub.nextFrontier ⟨digestCarry pub.nextPairIndex, hc⟩) =
              AppendPath.pathPrefix (PV_RunJoin_SpendDataMap.mapPublic f pub) pairL
                (digestCarry (PV_RunJoin_SpendDataMap.mapPublic f pub).nextPairIndex) := hfrontier
            _ = AppendPath.pathPrefix (PV_RunJoin_SpendDataMap.mapPublic f pub)
                  (PV_RunJoin_SpendDataMap.digest f pairK) (digestCarry pub.nextPairIndex) := by
                    rw [hpairValue]
                    rfl
            _ = PV_RunJoin_SpendDataMap.digest f
                  (AppendPath.pathPrefix pub pairK (digestCarry pub.nextPairIndex)) :=
                    (map_pathPrefix f pub pairK (digestCarry pub.nextPairIndex)).symm
  · rintro ⟨pairK, hpairK, hrootK, hcarryK⟩
    refine ⟨PV_RunJoin_SpendDataMap.digest f pairK, ?_, ?_, ?_⟩
    · rw [map_outputPair f pub, hpairK]
      rfl
    · calc
        (PV_RunJoin_SpendDataMap.mapPublic f pub).nextRoot = PV_RunJoin_SpendDataMap.digest f pub.nextRoot := rfl
        _ = PV_RunJoin_SpendDataMap.digest f (AppendPath.pathPrefix pub pairK 20) := congrArg _ hrootK
        _ = AppendPath.pathPrefix (PV_RunJoin_SpendDataMap.mapPublic f pub)
              (PV_RunJoin_SpendDataMap.digest f pairK) 20 := map_pathPrefix f pub pairK 20
    · intro hc
      have hcK : digestCarry pub.nextPairIndex < 20 := by
        simpa [PV_RunJoin_SpendDataMap.mapPublic] using hc
      calc
        (PV_RunJoin_SpendDataMap.mapPublic f pub).nextFrontier
            ⟨digestCarry (PV_RunJoin_SpendDataMap.mapPublic f pub).nextPairIndex, hc⟩ =
          PV_RunJoin_SpendDataMap.digest f (pub.nextFrontier ⟨digestCarry pub.nextPairIndex, hcK⟩) := rfl
        _ = PV_RunJoin_SpendDataMap.digest f
              (AppendPath.pathPrefix pub pairK (digestCarry pub.nextPairIndex)) :=
                congrArg (PV_RunJoin_SpendDataMap.digest f) (hcarryK hcK)
        _ = AppendPath.pathPrefix (PV_RunJoin_SpendDataMap.mapPublic f pub)
              (PV_RunJoin_SpendDataMap.digest f pairK)
              (digestCarry (PV_RunJoin_SpendDataMap.mapPublic f pub).nextPairIndex) := by
                rw [map_pathPrefix]
                rfl

#print axioms map_frozenEmpty
#print axioms map_step
#print axioms map_pathPrefix
#print axioms map_outputPair
#print axioms appendBinding_map_iff

#print axioms digest_injective
#print axioms digest_nodeCompress
#print axioms digest_zero
#print axioms map_frozenEmpty
#print axioms map_step
#print axioms map_pathPrefix
#print axioms map_outputPair
#print axioms appendBinding_map_iff

end R1Z.PV_RunJoin_AppendBindingMap
