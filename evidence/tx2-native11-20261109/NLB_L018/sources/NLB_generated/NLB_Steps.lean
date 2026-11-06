import NLB_C01
import NLB_C02
import NLB_C03
import NLB_C04
import NLB_C05
import NLB_C06
import NLB_C07
import NLB_C08
import NLB_C09
import NLB_QueryStep
set_option autoImplicit false
noncomputable section
namespace NLB_Parent
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- Auxiliary Result projections only: not complete child row packets. -/
def ResumeProjection (wr : NP6_StdModel.Reservation) (nativeResume : Resume) : Prop :=
 ∀ {H : Type} (d : aspis_core.digest.Digest32 H) (ck proof pub : Slice U8) (hash : H),
 nativeResume d ck proof pub hash=NJJ_Common.resume wr d ck proof pub .S2 hash

def MerkleProjection (nativeMerkle modelMerkle : Merkle) : Prop :=
 ∀ {H : Type} (d : aspis_core.digest.Digest32 H) (proof : Slice U8)
 (p : verifier.Prepared) (root : Array U8 32#usize) (hash : H),
 nativeMerkle d proof p root 1#usize hash=modelMerkle d proof p root 1#usize hash

/-- All nine local step equations installed in source order. The C01/C04
projections are intentionally visible and cannot be used as row-root premises. -/
theorem steps (wr rr fr : NP6_StdModel.Reservation) (loc : NIW_AlignFinishComposed.Locations)
 (nativeResume : Resume) (nativeMerkle modelMerkle : Merkle)
 (resumeProjection : ResumeProjection wr nativeResume)
 (merkleProjection : MerkleProjection nativeMerkle modelMerkle)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (e : Event) (entered : e∈(run wr rr modelMerkle (finish fr) d pub proof ck hash none).events) :
 window rr fr loc nativeResume nativeMerkle d hash e=e := by
 cases e with
 | resume c pr pu r => exact C01_step wr rr fr loc nativeResume nativeMerkle modelMerkle d pub proof ck hash c pr pu r entered (resumeProjection d c pr pu hash)
 | powers g r => exact C02_step wr rr fr loc nativeResume nativeMerkle modelMerkle d pub proof ck hash g r entered
 | inactive b r => exact C03_step wr rr fr loc nativeResume nativeMerkle modelMerkle d pub proof ck hash b r entered
 | merkle pr p root r => exact C04_step wr rr fr loc nativeResume nativeMerkle modelMerkle d pub proof ck hash pr p root r entered (merkleProjection d pr p root hash)
 | geometry qs n r => exact C05_step wr rr fr loc nativeResume nativeMerkle modelMerkle d pub proof ck hash qs n r entered
 | pending w r => exact C06_step wr rr fr loc nativeResume nativeMerkle modelMerkle d pub proof ck hash w r entered
 | query pr p a g geo pending r => exact C07_step wr rr fr loc nativeResume nativeMerkle modelMerkle d pub proof ck hash pr p a g geo pending r entered
 | flush b w r => exact C08_step wr rr fr loc nativeResume nativeMerkle modelMerkle d pub proof ck hash b w r entered
 | finish v p a r => exact C09_step wr rr fr loc nativeResume nativeMerkle modelMerkle d pub proof ck hash v p a r entered
#print axioms steps
end NLB_Parent
