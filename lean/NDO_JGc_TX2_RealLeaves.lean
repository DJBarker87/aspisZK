import NDO_JGc_TX2_M2LeafSources10
import NDO_JGc_TX2_M2LeafSources14
import NDO_JGc_TX2_M2LeafSources18
import RPt_JFn_Values
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_RealLeaves
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

def dictionary {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) :
    AspisR1Stage2.aspis_core.digest.Digest32 Hash :=
  {D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts}

def value (i : Fin 12) : State := match i.val with
  | 0 => JGc_TX2_M2Roots.value000
  | 1 => JGc_TX2_M2Roots.value001
  | 2 => JGc_TX2_M2Roots.value002
  | 3 => JGc_TX2_M2Roots.value003
  | 4 => JGc_TX2_M2Roots.value004
  | 5 => JGc_TX2_M2Roots.value005
  | 6 => JGc_TX2_M2Roots.value006
  | 7 => JGc_TX2_M2Roots.value007
  | 8 => JGc_TX2_M2Roots.value008
  | 9 => JGc_TX2_M2Roots.value009
  | 10 => JGc_TX2_M2Roots.value010
  | _ => JGc_TX2_M2Roots.value011

def Calls {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) : Prop :=
  ∀ i : Fin 12, Port4B_LeafCode.native (dictionary D) hash 2#usize
    (JFo_Opening.value (JFn_Values.position i))=ok (encodeState (value i))

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) : Calls D hash := by
  intro i
  fin_cases i
  · exact JGc_TX2_M2Leaf10.source D hash
  · exact JGc_TX2_M2Leaf11.source D hash
  · exact JGc_TX2_M2Leaf12.source D hash
  · exact JGc_TX2_M2Leaf13.source D hash
  · exact JGc_TX2_M2Leaf14.source D hash
  · exact JGc_TX2_M2Leaf15.source D hash
  · exact JGc_TX2_M2Leaf16.source D hash
  · exact JGc_TX2_M2Leaf17.source D hash
  · exact JGc_TX2_M2Leaf18.source D hash
  · exact JGc_TX2_M2Leaf19.source D hash
  · exact JGc_TX2_M2Leaf20.source D hash
  · exact JGc_TX2_M2Leaf21.source D hash
#print axioms source
end AspisR1.JGc_TX2_RealLeaves
end
