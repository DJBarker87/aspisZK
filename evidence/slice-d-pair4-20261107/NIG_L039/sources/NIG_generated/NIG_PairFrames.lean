import NIG_CommonPost
import NIG_LowPost
import NIG_LibraDomain
import NHX_RegularPost
import NHX_HighPost
import NHX_FactoredPacket
import NHM_SharedPartialResult
import NHX_FinalTotal
import NIG_FilledCoverage
set_option autoImplicit false
noncomputable section
namespace NIG_PairFrames
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
abbrev W:=FIo_Native.weights.Weights
abbrev Powers:=Array NE 4#usize
abbrev Parts:=Array NE 7#usize
abbrev Scratch:=alloc.vec.Vec NQ
abbrev RUnit:=core.result.Result Unit FIo_Native.verifier.Error
variable [FIo_Native.Allocation]

def canon {n:Usize} (a:Array NE n):Prop:=∀ x∈a.val,canonE x

def initial:Parts:=Array.repeat 7#usize NHI_Scalar.zero

theorem initial_canonical:canon initial:=by
 intro x hx
 simp only [initial,Array.repeat,List.mem_replicate] at hx
 exact hx.2 ▸ NHI_Scalar.zero_canonical

/-- This is an observed returning arm, not an assumption of allocator
availability: the enclosing driver still branches on the complete reply. -/
theorem filled (r:NP6_StdModel.Reservation) (v:Scratch)
 (run:letI:=FIo_Install.allocation r
  FIo_Native.aspis_core.r0.heap.filled FIo_Native.aspis_core.field.QM31.Insts.CoreMarkerCopy
   64#usize NHX_FilledZero.zeroQ=ok (.Ok v)):
 NHX_RegularPost.Inv v initial:=by
 rw [NHI_FilledModel.qm] at run
 cases r with
 | Err e=>cases run
 | Ok u=>
  cases u
  change ok (.Ok (NHI_FilledModel.vector 64#usize NHX_FilledZero.zeroQ))=ok (.Ok v) at run
  cases core.result.Result.Ok.inj (Result.ok.inj run)
  exact ⟨NHI_FilledModel.canonical _ _ NHX_FilledZero.zero_canonical,
   NHI_FilledModel.length _ _,initial_canonical⟩

theorem regular (w:W) (b:Bool) (alpha:Slice NE) (f:Slice U8) (ap0 ap1:Powers)
 (s2:w.variant=FIo_Native.transport.Variant.S2) (hf:NHI_TensorOuterStep.Factors w)
 (ha:canon ap0) (hb:canon ap1) (before after:Scratch) (parts out:Parts)
 (reply:RUnit) (hi:NHX_RegularPost.Inv before parts)
 (run:FIo_Native.weights.process_regular_kinds w b alpha f 2#usize 64#usize ap0 ap1 before parts=ok (reply,after,out)):
 NHX_RegularPost.Inv after out:=
 NHX_RegularPost.source w b alpha f ap0 ap1 s2 hf ha hb before after parts out reply hi run

theorem common (w:W) (hf:NHI_TensorOuterStep.Factors w)
 (w1:W) (cells:Array NQ 16#usize)
 (run:FIo_Native.weights.Weights.pair_loop1 {start:=0#usize,«end»:=16#usize} w
  (Array.repeat 16#usize NHX_FilledZero.zeroQ)=ok (w1,cells)):
 w1=w ∧ NHI_CellCanon.array cells:=by
 apply NIG_CommonPost.source w hf _ (by
  intro q hq
  simp only [Array.repeat,List.mem_replicate] at hq
  exact hq.2 ▸ NHX_FilledZero.zero_canonical) (w1,cells) run

theorem partials (f:Slice U8) (common:Array NQ 16#usize) (out:Powers)
 (run:FIo_Native.weights.shared_partials f common=ok (.Ok out)):canon out:=
 NHM_SharedPartialResult.source f common out run

theorem high (partials:Powers) (w:W) (ap0 ap1:Powers) (parts after:Parts)
 (hf:NHI_TensorOuterStep.Factors w) (ha:canon ap0) (hb:canon ap1) (hp:canon parts)
 (reply:RUnit) (run:FIo_Native.weights.shared_high partials w ap0 ap1 parts=ok (reply,after)):
 canon after ∧ NHX_HighPost.Frame parts after:=by
 rw [NHX_HighReference.source] at run
 exact NHX_HighPost.post partials w ap0 ap1 parts after hf ha hb hp reply run

theorem low (ap0 ap1:Powers) (ha:canon ap0) (hb:canon ap1) (out:Array NE 16#usize)
 (run:FIo_Native.weights.Weights.pair_loop15 {start:=0#usize,«end»:=16#usize} ap0 ap1
  (Array.repeat 16#usize NHI_Scalar.zero)=ok out):canon out:=by
 apply NIG_LowPost.source ap0 ap1 ha hb _ out (by
  intro x hx
  simp only [Array.repeat,List.mem_replicate] at hx
  exact hx.2 ▸ NHI_Scalar.zero_canonical) run

theorem factored (w:W) (ap0 ap1:Powers) (ha:canon ap0) (hb:canon ap1)
 (he:NHI_CellCanon.array w.extra) (out:Powers)
 (run:FIo_Native.weights.factored_s2_libra_weights ap0 ap1 w.extra=ok out):canon out:=by
 obtain ⟨result,source,model,canonical⟩:=NHX_FactoredPacket.source ap0 ap1 w.extra ha hb he
 cases Result.ok.inj (source.symm.trans run)
 exact canonical

#print axioms initial_canonical
#print axioms filled
#print axioms regular
#print axioms common
#print axioms partials
#print axioms high
#print axioms low
#print axioms factored
end NIG_PairFrames
