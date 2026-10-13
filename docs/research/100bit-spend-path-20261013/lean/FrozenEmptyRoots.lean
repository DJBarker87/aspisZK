import R1EmptyRootZeroCheck
import R1EmptyRoot01Check
import R1EmptyRoot02Check
import R1EmptyRoot03Check
import R1EmptyRoot04Check
import R1EmptyRoot05Check
import R1EmptyRoot06Check
import R1EmptyRoot07Check
import R1EmptyRoot08Check
import R1EmptyRoot09Check
import R1EmptyRoot10Check
import R1EmptyRoot11Check
import R1EmptyRoot12Check
import R1EmptyRoot13Check
import R1EmptyRoot14Check
import R1EmptyRoot15Check
import R1EmptyRoot16Check
import R1EmptyRoot17Check
import R1EmptyRoot18Check
import R1EmptyRoot19Check
import R1EmptyRoot20Check
import R1PoseidonMap

/-! The literal empty-root table equals its hash recurrence. Every concrete
node is supplied by a round-split kernel certificate over M31; ring-hom
naturality transfers it to any field of the same characteristic. This
is a field-model fact, not a Rust implementation-refinement theorem. -/
set_option autoImplicit false
namespace AspisR1.FrozenEmptyRoots
open R0P AspisCircleGroupOrder

attribute [local irreducible] nodeCompress poseidonPermutation

theorem successor_base (level : Fin 20) :
    AppendNode.frozenEmpty (K := ZMod P) level.succ =
      nodeCompress (AppendNode.frozenEmpty level.castSucc)
        (AppendNode.frozenEmpty level.castSucc) := by
  fin_cases level
  · exact AspisR1.EmptyRoot01Check.node_base
  · exact AspisR1.EmptyRoot02Check.node_base
  · exact AspisR1.EmptyRoot03Check.node_base
  · exact AspisR1.EmptyRoot04Check.node_base
  · exact AspisR1.EmptyRoot05Check.node_base
  · exact AspisR1.EmptyRoot06Check.node_base
  · exact AspisR1.EmptyRoot07Check.node_base
  · exact AspisR1.EmptyRoot08Check.node_base
  · exact AspisR1.EmptyRoot09Check.node_base
  · exact AspisR1.EmptyRoot10Check.node_base
  · exact AspisR1.EmptyRoot11Check.node_base
  · exact AspisR1.EmptyRoot12Check.node_base
  · exact AspisR1.EmptyRoot13Check.node_base
  · exact AspisR1.EmptyRoot14Check.node_base
  · exact AspisR1.EmptyRoot15Check.node_base
  · exact AspisR1.EmptyRoot16Check.node_base
  · exact AspisR1.EmptyRoot17Check.node_base
  · exact AspisR1.EmptyRoot18Check.node_base
  · exact AspisR1.EmptyRoot19Check.node_base
  · exact AspisR1.EmptyRoot20Check.node_base

theorem map_frozenEmpty {K L : Type} [Field K] [Field L]
    (f : K →+* L) (level : Fin 21) :
    PoseidonMap.mapDigest f (AppendNode.frozenEmpty level) =
      AppendNode.frozenEmpty level := by
  funext i
  exact map_natCast f (emptyRootsNat level i)

theorem initial {K : Type} [Field K] [CharP K P] :
    AppendNode.frozenEmpty (K := K) 0 =
      nodeCompress (fun _ => 0) (fun _ => 0) := by
  let f : ZMod P →+* K := ZMod.castHom (dvd_refl P) K
  have h := congrArg (PoseidonMap.mapDigest f) EmptyRootZeroCheck.node_zero_base
  rw [map_frozenEmpty, PoseidonMap.map_nodeCompress] at h
  have hz : PoseidonMap.mapDigest f (fun _ => 0) = fun _ => 0 := by
    funext i
    exact map_zero f
  rw [hz] at h
  exact h

theorem successor {K : Type} [Field K] [CharP K P] (level : Fin 20) :
    AppendNode.frozenEmpty (K := K) level.succ =
      nodeCompress (AppendNode.frozenEmpty level.castSucc)
        (AppendNode.frozenEmpty level.castSucc) := by
  let f : ZMod P →+* K := ZMod.castHom (dvd_refl P) K
  have h := congrArg (PoseidonMap.mapDigest f) (successor_base level)
  rw [map_frozenEmpty, PoseidonMap.map_nodeCompress, map_frozenEmpty] at h
  exact h

#print axioms successor_base
#print axioms map_frozenEmpty
#print axioms initial
#print axioms successor
end AspisR1.FrozenEmptyRoots
