import NDO_JGh_TX2_M0LeafSources10
import NDO_JGh_TX2_M0LeafSources12
import NDO_JGh_TX2_M0LeafSources14
import NDO_JGh_TX2_M0LeafSources16
import NDO_JGh_TX2_M0LeafSources18
import NDO_JGh_TX2_M0LeafSources20
import NDO_JGh_TX2_M1LeafSources10
import NDO_JGh_TX2_M1LeafSources12
import NDO_JGh_TX2_M1LeafSources14
import NDO_JGh_TX2_M1LeafSources16
import NDO_JGh_TX2_M1LeafSources18
import NDO_JGh_TX2_M1LeafSources20
import NDO_JGc_TX2_RealLeaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGk_TX2_NativeLeaves
open Aeneas Aeneas.Std Result
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
def value0 (i : Fin 12) : State := match i.val with
  | 0 => JGf_TX2_M0Roots.value000
  | 1 => JGf_TX2_M0Roots.value001
  | 2 => JGf_TX2_M0Roots.value002
  | 3 => JGf_TX2_M0Roots.value003
  | 4 => JGf_TX2_M0Roots.value004
  | 5 => JGf_TX2_M0Roots.value005
  | 6 => JGf_TX2_M0Roots.value006
  | 7 => JGf_TX2_M0Roots.value007
  | 8 => JGf_TX2_M0Roots.value008
  | 9 => JGf_TX2_M0Roots.value009
  | 10 => JGf_TX2_M0Roots.value010
  | _ => JGf_TX2_M0Roots.value011
theorem source0 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) (i : Fin 12) :
    Port4B_LeafCode.native (JGc_TX2_RealLeaves.dictionary D) hash 0#usize
      (JFo_Opening.value (JFn_Values.position i))=ok (encodeState (value0 i)) := by
  fin_cases i
  · exact JGh_TX2_M0Leaf10.source D hash
  · exact JGh_TX2_M0Leaf11.source D hash
  · exact JGh_TX2_M0Leaf12.source D hash
  · exact JGh_TX2_M0Leaf13.source D hash
  · exact JGh_TX2_M0Leaf14.source D hash
  · exact JGh_TX2_M0Leaf15.source D hash
  · exact JGh_TX2_M0Leaf16.source D hash
  · exact JGh_TX2_M0Leaf17.source D hash
  · exact JGh_TX2_M0Leaf18.source D hash
  · exact JGh_TX2_M0Leaf19.source D hash
  · exact JGh_TX2_M0Leaf20.source D hash
  · exact JGh_TX2_M0Leaf21.source D hash
#print axioms source0
def value1 (i : Fin 12) : State := match i.val with
  | 0 => JGh_TX2_M1Roots.value000
  | 1 => JGh_TX2_M1Roots.value001
  | 2 => JGh_TX2_M1Roots.value002
  | 3 => JGh_TX2_M1Roots.value003
  | 4 => JGh_TX2_M1Roots.value004
  | 5 => JGh_TX2_M1Roots.value005
  | 6 => JGh_TX2_M1Roots.value006
  | 7 => JGh_TX2_M1Roots.value007
  | 8 => JGh_TX2_M1Roots.value008
  | 9 => JGh_TX2_M1Roots.value009
  | 10 => JGh_TX2_M1Roots.value010
  | _ => JGh_TX2_M1Roots.value011
theorem source1 {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) (i : Fin 12) :
    Port4B_LeafCode.native (JGc_TX2_RealLeaves.dictionary D) hash 1#usize
      (JFo_Opening.value (JFn_Values.position i))=ok (encodeState (value1 i)) := by
  fin_cases i
  · exact JGh_TX2_M1Leaf10.source D hash
  · exact JGh_TX2_M1Leaf11.source D hash
  · exact JGh_TX2_M1Leaf12.source D hash
  · exact JGh_TX2_M1Leaf13.source D hash
  · exact JGh_TX2_M1Leaf14.source D hash
  · exact JGh_TX2_M1Leaf15.source D hash
  · exact JGh_TX2_M1Leaf16.source D hash
  · exact JGh_TX2_M1Leaf17.source D hash
  · exact JGh_TX2_M1Leaf18.source D hash
  · exact JGh_TX2_M1Leaf19.source D hash
  · exact JGh_TX2_M1Leaf20.source D hash
  · exact JGh_TX2_M1Leaf21.source D hash
#print axioms source1
end AspisR1.JGk_TX2_NativeLeaves
end
