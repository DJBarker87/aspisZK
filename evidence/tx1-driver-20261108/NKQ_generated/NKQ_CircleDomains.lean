import NKA_FinishStages
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKQ_CircleDomains
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- Both actual caller slots, at arbitrary actual transcript carries. The
second carry is universally quantified, so the real first call's returned
carry is eligible without selecting an independent successful execution. -/
theorem source {Pointer H : Type} (D : aspis_core.Digest32 H)
 (template : NIX_DispatchCut.Pre Pointer) (bytes : Slice U8)
 (beforeFirst beforeSecond : r1_wire.SemanticTranscript H) :
 match parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes with
 | .ok (.Ok pre) =>
   ∃ first second,
    r1_wire.Prefix.validated_record (PrefixAdapter.fromOld pre) 25#u8=ok (.Ok first) ∧
    r1_wire.Prefix.validated_record (PrefixAdapter.fromOld pre) 26#u8=ok (.Ok second) ∧
    first.row=25#u8 ∧ second.row=26#u8 ∧
    NJM_InvocationRoots.Circle D template beforeFirst first ∧
    NJM_InvocationRoots.Circle D template beforeSecond second
 | _ => True := by
 split
 · rename_i pre parsed
   have a:=NJM_InvocationRoots.circle D template bytes beforeFirst ⟨25,by decide⟩
   have b:=NJM_InvocationRoots.circle D template bytes beforeSecond ⟨26,by decide⟩
   rw [parsed] at a b
   obtain ⟨first,ga,ta,pa⟩:=a
   obtain ⟨second,gb,tb,pb⟩:=b
   exact ⟨first,second,ga,gb,ta,tb,pa,pb⟩
 · trivial
#print axioms source
#print source
end AspisR1.NKQ_CircleDomains
end
