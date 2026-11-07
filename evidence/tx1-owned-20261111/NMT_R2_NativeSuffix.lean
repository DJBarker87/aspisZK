import NMT_R2_NativeSpecs
import NMT_R2_345Return
import NMT_R2_Scalar
import NMT_R2_Lengths
import NMT_345TailFrames
set_option autoImplicit false
noncomputable section
namespace NMT_R2_NativeSuffix
open Aeneas Aeneas.Std NMT_345 RSL NMT_345Observation NMT_R2_NativeSpecs

structure Point (W : Type) extends Bounds W where
 proofView : Slice U8
 k : Usize
 validated : NMT_R2_PublicLibrary.valid statement = true

def args {W : Type} (p : Point W) : Args328 :=
 ⟨semanticValue p.statement,p.publicData,p.proofView,p.k⟩

def returned (length : Usize) (bytes : alloc.vec.Vec U8) : Obs (core.result.Result (alloc.vec.Vec U8) PE) :=
 ⟨.ret (if alloc.vec.Vec.len bytes != length then .Err .InvalidAccountData else .Ok bytes),[]⟩

def run {W : Type} (child : Args328 → Env → Obs (core.result.Result (alloc.vec.Vec U8) PE))
 (p : Point W) (env : Env) : Obs (core.result.Result (alloc.vec.Vec U8) PE) :=
 bindObs (child (args p) env) fun r =>
 match r with | .Ok bytes => returned (Slice.len p.checkpointData) bytes | .Err e => ⟨.ret (.Err e),[]⟩

theorem returned_observation (ck : Slice U8) (bytes : alloc.vec.Vec U8) :
 observation (returned (Slice.len ck) bytes) =
 NMT_R2_345.stepReturn (ck.val.map byte).length (bytes.val.map byte) := by
 unfold returned observation NMT_R2_345.stepReturn
 have same := NMT_R2_Scalar.usize_compare (alloc.vec.Vec.len bytes) (Slice.len ck)
 simp only [List.length_map]
 rw [← same,NMT_R2_Lengths.vec,NMT_R2_Lengths.slice]
 cases h : bytes.val.length != ck.val.length <;> rfl

/-- Full native suffix: the complete child packet, original semantic public,
public/proof/k arguments, every child event, later length rejection and stop
prefix. The public clause comes from the SAME reached validator result. -/
theorem law {W : Type} (V : VLib) (encodePublic : Public → V.Public)
 (P : PreparedNew (NMT_R2_PublicLibrary.withPublic V encodePublic))
 (child : Args328 → Env → Obs (core.result.Result (alloc.vec.Vec U8) PE))
 (packet : RowSpec328 V encodePublic P child) (p : Point W) (env : Env) :
 RS.bind (Spec.call (NMT_R2.TX1_328.Domain (NMT_R2_PublicLibrary.withPublic V encodePublic))
  (NMT_R2.TX1_328.Ref (NMT_R2_PublicLibrary.withPublic V encodePublic) P)
  (args328 V encodePublic (args p)))
  (fun bytes => RS.seq (RS.check (bytes.length != (p.checkpointData.val.map byte).length) .invalidAccountData)
   (RS.pure bytes)) env (observation (run child p env)) := by
 have hd : publicDomain (args p).public_ := NMT_R2_PublicLibrary.semantic_domain p.statement p.validated
 have first := packet (args p) env hd
 have firstCall : Spec.call (NMT_R2.TX1_328.Domain (NMT_R2_PublicLibrary.withPublic V encodePublic))
  (NMT_R2.TX1_328.Ref (NMT_R2_PublicLibrary.withPublic V encodePublic) P)
  (args328 V encodePublic (args p)) env (observation (child (args p) env)) := ⟨hd,first⟩
 unfold run
 cases h : child (args p) env with
 | mk exit events =>
  rw [h] at firstCall
  cases exit with
  | abort => exact Or.inr (Or.inl ⟨events,firstCall,rfl⟩)
  | diverge => exact Or.inr (Or.inr ⟨events,firstCall,rfl⟩)
  | ret r =>
   cases r with
   | Err e => exact Or.inl ⟨.error (pe e),events,⟨.ret (.error (pe e)),[]⟩,firstCall,rfl,rfl⟩
   | Ok bytes =>
    have later := NMT_R2_345.stepReturn_valid (p.checkpointData.val.map byte).length (bytes.val.map byte) env
    rw [← returned_observation] at later
    exact Or.inl ⟨.ok (bytes.val.map byte),events,observation (returned (Slice.len p.checkpointData) bytes),
     firstCall,later,rfl⟩
#print axioms returned_observation
#print axioms law
end NMT_R2_NativeSuffix
end
