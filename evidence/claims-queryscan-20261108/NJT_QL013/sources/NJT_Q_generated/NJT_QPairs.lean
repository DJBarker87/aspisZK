import NJT_QDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJT_QPairs
open Aeneas Aeneas.Std Result NJT_QBase NGQ_SamplerDriver
open Query31ExplicitListLoop

def nativeScan (native : NJT_QScan.Native) (s : State) (b : Bytes) : Result (Bool×State) :=
 let value:=NJT_QScan.run native (words b).val s
 ok (optionStop value.2,value.1)

/-- Child Results are installed at the same block/state by induction. The
native outer cut selects advance[k] exactly on true and retains advance7 on
continuation; the source carries that state through NHB_OuterState.walk. -/
theorem walk_source (native : NJT_QScan.Native) (cut : NJT_QScan.Cut native)
 (advances : Blocks) (fallback : Usize) (inputs : List (Bytes32×Usize))
 (s : State) (domain : NJT_QDomains.Domain s) :
 NGQ_SamplerDriver.walk NGQ_SamplerPacket.Scan advances fallback inputs s=
  NGQ_SamplerDriver.walk (nativeScan native) advances fallback inputs s := by
 induction inputs generalizing s with
 | nil => rfl
 | cons head tail ih =>
  have call:=NJT_QScan.scan native cut s domain.1 head.1
  simp only [NGQ_SamplerDriver.walk,NGQ_SamplerPacket.Scan,call,nativeScan,bind_tc_ok]
  dsimp only
  split
  · rfl
  · exact ih _ (NJT_QDomains.scan_preserved native cut head.1 s domain)

/-- Query31/NHK's reviewed queries_from_pairs reference on exactly its original
8x32-byte arrays, same default state, first-stop convention and full Result.
No use or closure of the ledger's conservative TX1:202 child is asserted. -/
theorem reference (native : NJT_QScan.Native) (cut : NJT_QScan.Cut native)
 (blocks advances : Blocks) :
 AspisR1Query31Transcript.queries_from_pairs_with_scan NGQ_SamplerPacket.Scan
  NGQ_SamplerPacket.initial blocks advances=
  NGQ_SamplerDriver.walk (nativeScan native) advances 7#usize
   (blocks.val.zip [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize])
   NGQ_SamplerPacket.initial := by
 rw [NGQ_SamplerDriver.source]
 exact walk_source native cut advances _ _ _ NJT_QDomains.initial

#print axioms walk_source
#print axioms reference
#check @reference
end AspisR1.NJT_QPairs
end
