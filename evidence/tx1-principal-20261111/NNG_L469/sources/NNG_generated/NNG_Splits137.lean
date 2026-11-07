import NNG_Tree137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Splits137
open Aeneas Aeneas.Std NMP_prepare NNG_Context137 NMT_CallTree

theorem publicTranscript {H : Type} (c : Calls) (s : Parent H) (p : r1_wire.Prefix) :
    NNG_Tree137.publicTranscript c s p = NMT_CallTree.bind
      (invoke "TX1:131/public_transcript" (s.publicValue,s.hash,p.c1_root)
        (c.publicTranscript s.digest s.publicValue s.hash p.c1_root))
      (fun reply=>match reply with
        | .Err e=>pure (.Err e)
        | .Ok t=>NNG_Tree137.begin_ c s p t) := by rfl
#print axioms publicTranscript
end AspisR1.NNG_Splits137
