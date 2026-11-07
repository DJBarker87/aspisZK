import LIBB_PoolLib
import LIBB_ScanNoWrite
set_option autoImplicit false
noncomputable section
namespace LIBB_PoolNoWrite
open Aeneas Aeneas.Std
open RSL NMV_NoWrite

theorem reconstruct_source (q : LIBB_PoolCarriers.Request) (a : LIBB_AuthCarrier.Raw)
 (c : LIBB_PoolCarriers.Afterstate) : Free (NMS_R2N_ReconstructSites.meaning q a c) := by
 unfold NMS_R2N_ReconstructSites.meaning
 split
 · apply bind_free _ _ alloc_free
   intro unit
   apply bind_free _ _ alloc_free
   intro unit
   exact LIBB_NoWriteGraph.lift _
 · exact LIBB_NoWriteGraph.lift _

theorem reconstruct (q : LIBB_PoolCarriers.Request) (a : Authenticated) (c : LIBB_PoolCarriers.Afterstate) :
 Free (LIBB_PoolReconstruct.reconstruct q a c) := by
 unfold LIBB_PoolReconstruct.reconstruct
 cases LIBB_AuthCarrier.raw a with
 | none => exact panic_free
 | some raw => exact LIBB_NoWriteGraph.map _ _ (reconstruct_source q raw c)

theorem encode (s : LIBB_PoolCarriers.Statement) : Free (LIBB_PoolEncode.encodeStatement s) :=
 LIBB_NoWriteGraph.map _ _ (LIBB_NoWriteGraph.lift _)

theorem emit (s : LIBB_PoolCarriers.Statement) : Free (LIBB_PoolEmit.emitResult s) := by
 intro env o h cell bytes member
 subst o
 unfold LIBB_PoolEmit.observation at member
 cases code : LIBB_PoolEmit.code s with
 | fail e => simp only [code,List.not_mem_nil] at member
 | div => simp only [code,List.not_mem_nil] at member
 | ok reply =>
   cases reply with
   | Err e => simp only [code,List.not_mem_nil] at member
   | Ok st =>
     simp only [code] at member
     obtain ⟨e,_,equal⟩ := List.mem_map.mp member
     cases e with
     | setReturnData b => cases equal
     | other impossible => exact nomatch impossible

/-- Concrete G2 library effects package; no arbitrary PoolLaws premise. -/
def laws : PoolLaws LIBB_PoolLib.library where
 scan := LIBB_ScanNoWrite.scan
 reconstruct := reconstruct
 encode := encode
 emit := emit
#print axioms reconstruct_source
#print axioms reconstruct
#print axioms encode
#print axioms emit
#print axioms laws
end LIBB_PoolNoWrite
end
