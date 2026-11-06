import NJR_ChecksumDomain
set_option autoImplicit false
noncomputable section
namespace NJR_ChecksumAtHeadline
open Aeneas Aeneas.Std Result AspisR1 S2W_NativeConsolidation S2W_ExtractionBoundary

/-- Derive checksum scope on the SAME witnesses produced by the existing
accepted native pair. No SourceCuts, successful parser/finish, public/proof
length, or independently chosen buffers are additional premises. This is an
auxiliary caller theorem over the existing extraction boundary, not a positive
TX2:065 native bridge with arbitrary base/finish parameters. -/
theorem accepted_pair {F : Type} (adapter : AdapterRw.Ops) (base : VTop_Stages.Ops)
 (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
 (native1 : First) (native2 : Second)
 (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
 (extraction : AeneasExtraction (Tx2I_Install.install adapter base finish) native1 native2 hashv)
 (program : Program) (accounts1 accounts2 : Accounts) (data1 data2 : Slice U8)
 (slot : Slot) (saved : alloc.vec.Vec U8)
 (accepted1 : native1 program accounts1 data1=ok (.Ok saved))
 (accepted2 : native2 program accounts2 data2 slot=ok (.Ok ())) :
 ∃ f s,SourceCuts (Tx2I_Install.install adapter base finish) accounts1 accounts2 saved f s ∧
  NJR_ChecksumDomain.Scope s.pub s.proof := by
 obtain ⟨f,s,cuts⟩:=cuts_of_acceptance _ native1 native2 hashv extraction program accounts1 accounts2
  data1 data2 slot saved accepted1 accepted2
 exact ⟨f,s,cuts,NJR_ChecksumDomain.of_source_cuts adapter base finish accounts1 accounts2 saved f s cuts⟩

#print accepted_pair
#print axioms accepted_pair
end NJR_ChecksumAtHeadline
