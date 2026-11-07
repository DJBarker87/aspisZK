import NNG_PublicSource137
import NNG_EmittedCallGraph
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PublicProjection137
open Aeneas Aeneas.Std Result NMP_prepare NMP_Transport
open NMP_ResultTransport (outer)

def decode : core.result.Result (r1_wire.SemanticTranscript Unit) r1_wire.Error → Except LIB_VCarriers.WErr LIB_VCarriers.Transcript
 | .Ok t=>.ok (toT10 t) | .Err e=>.error (toT12 e)

theorem root (p : LIB_VCarriers.Prefix) :
    (fromT13 (LIB_VCarriers.prefixRaw p)).c1_root=LIB_Env.nativeKey (LIB_VCarriers.c1Root p) :=
  (NNG_PublicSource137.key_native p.parsed.c1_root).symm
#print axioms root

theorem projected (env : RSL.Env) (pub : LIB_VCarriers.Public) (p : LIB_VCarriers.Prefix) :
    NNG_EmittedCallGraph.resultMap decode
      (NMP_Install131.publicTranscript (NNG_PublicSource137.digest env) (fromT9 pub) ()
        (fromT13 (LIB_VCarriers.prefixRaw p)).c1_root) =
      NNG_EmittedCallGraph.resultMap LIB_VRecords.host
        (AspisR1PublicPreparation.PreparedHashCode.run (AspisR1PublicPreparation.S1SemanticCode.publicTranscript (LIB_VCode.digest env) pub ()
          (LIB_Env.nativeKey (LIB_VCarriers.c1Root p)))).2 := by
  rw [NNG_PublicSource137.value,fromT9_inverse,root]
  generalize (AspisR1PublicPreparation.PreparedHashCode.run (AspisR1PublicPreparation.S1SemanticCode.publicTranscript (LIB_VCode.digest env) pub ()
    (LIB_Env.nativeKey (LIB_VCarriers.c1Root p)))).2 = out
  cases out with
  | fail e=>rfl
  | div=>rfl
  | ok out=>cases out <;> simp only [outer,NMP_ResultTransport.inner,NNG_EmittedCallGraph.resultMap,decode,LIB_VRecords.host,fromT10_inverse,fromT12_inverse]
#print axioms projected
end AspisR1.NNG_PublicProjection137
