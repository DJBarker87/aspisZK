import NNU_CommonSelected
import Tx2N_Powers
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOF_PowersAssociation
open Aeneas Aeneas.Std Result VTop_Stages

/-- Canonical native wide values are determined by their decoded value.
Coordinatewise use of the compiled SAQ_Inverse.canonical_injective (present in
the NNU closure); the native records are destructured explicitly because this
generation of FIo_NativeTypes has no ext lemmas. -/
theorem identify (x y : FIo_Install.NE) (hx : FIo_WideValues.Canon x)
 (hy : FIo_WideValues.Canon y)
 (same : AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide x)=
   AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide y)) : x=y := by
 rcases x with ⟨⟨⟨x0,x1⟩,⟨x2,x3⟩⟩,⟨⟨x4,x5⟩,⟨x6,x7⟩⟩⟩
 rcases y with ⟨⟨⟨y0,y1⟩,⟨y2,y3⟩⟩,⟨⟨y4,y5⟩,⟨y6,y7⟩⟩⟩
 obtain rfl : x0=y0 := SAQ_Inverse.canonical_injective x0 y0 hx.1.1.1 hy.1.1.1
  (congrArg (fun z => z.re.re.re) same)
 obtain rfl : x1=y1 := SAQ_Inverse.canonical_injective x1 y1 hx.1.1.2 hy.1.1.2
  (congrArg (fun z => z.re.re.im) same)
 obtain rfl : x2=y2 := SAQ_Inverse.canonical_injective x2 y2 hx.1.2.1 hy.1.2.1
  (congrArg (fun z => z.re.im.re) same)
 obtain rfl : x3=y3 := SAQ_Inverse.canonical_injective x3 y3 hx.1.2.2 hy.1.2.2
  (congrArg (fun z => z.re.im.im) same)
 obtain rfl : x4=y4 := SAQ_Inverse.canonical_injective x4 y4 hx.2.1.1 hy.2.1.1
  (congrArg (fun z => z.im.re.re) same)
 obtain rfl : x5=y5 := SAQ_Inverse.canonical_injective x5 y5 hx.2.1.2 hy.2.1.2
  (congrArg (fun z => z.im.re.im) same)
 obtain rfl : x6=y6 := SAQ_Inverse.canonical_injective x6 y6 hx.2.2.1 hy.2.2.1
  (congrArg (fun z => z.im.im.re) same)
 obtain rfl : x7=y7 := SAQ_Inverse.canonical_injective x7 y7 hx.2.2.2 hy.2.2.2
  (congrArg (fun z => z.im.im.im) same)
 rfl

/-- The resumed gamma is canonical in the native carrier. -/
theorem canonical_gamma (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NID_ResumeFields.Domain p a) :
 FIo_WideValues.Canon (FIo_Install.toE p.gamma) := by
 rcases domain.gamma with ⟨⟨x0,x1,x2,x3⟩,⟨x4,x5,x6,x7⟩⟩
 exact ⟨⟨⟨x0,x1⟩,⟨x2,x3⟩⟩,⟨⟨x4,x5⟩,⟨x6,x7⟩⟩⟩

/-- The resumed gamma is canonical in the early-powers carrier. -/
theorem canonical_early (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NID_ResumeFields.Domain p a) :
 AspisR1LoopPowers.Canonical (Tx2N_Powers.toPowers p.gamma) := by
 rcases domain.gamma with ⟨⟨x0,x1,x2,x3⟩,⟨x4,x5,x6,x7⟩⟩
 exact ⟨⟨⟨x0,x1⟩,⟨x2,x3⟩⟩,⟨⟨x4,x5⟩,⟨x6,x7⟩⟩⟩

/-- Early-carrier canonicity is native-carrier canonicity of the same record. -/
theorem canonical_of_early (x : Tx2N_Powers.E)
 (h : AspisR1LoopPowers.Canonical (Tx2N_Powers.toPowers x)) :
 FIo_WideValues.Canon (FIo_Install.toE x) := by
 obtain ⟨⟨⟨x0,x1⟩,⟨x2,x3⟩⟩,⟨⟨x4,x5⟩,⟨x6,x7⟩⟩⟩ := h
 exact ⟨⟨⟨x0,x1⟩,⟨x2,x3⟩⟩,⟨⟨x4,x5⟩,⟨x6,x7⟩⟩⟩

/-- The two decoders agree on the same record (nominal carrier copies). -/
theorem decode_link (x : Tx2N_Powers.E) :
 AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide (FIo_Install.toE x)) =
 AspisR1LoopPowers.decode (Tx2N_Powers.toPowers x) := rfl

/-- Powers-carrier association: on the resumed Domain, a successful source
NHT_PacketOps.powers reply is also the installed Tx2N_Powers.powers reply. -/
theorem source (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NID_ResumeFields.Domain p a)
 (out : Array Tx2N_Powers.E 29#usize)
 (called : NHT_PacketOps.powers 29#usize p.gamma=ok out) :
 Tx2N_Powers.powers 29#usize p.gamma=ok out := by
 obtain ⟨native,nativeCall,associated⟩ := Port3_PushFrame.bind_success _ _ _ called
 have sameOut : FIp_DotsAdapter.fromArray native=out := Result.ok.inj associated
 obtain ⟨early,earlyCall,earlyValues⟩ :=
  Tx2N_Powers.total_exact 29#usize p.gamma (canonical_early p a domain)
 have nativeValues :=
  FIp_PowersValue.powers 29#usize _ native (canonical_gamma p a domain) nativeCall
 have same : early=FIp_DotsAdapter.fromArray native := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp only [early.property,FIp_DotsAdapter.fromArray,List.length_map,native.property]
  · intro j hj _
    have hjN : j<(29#usize).val := by rw [early.property] at hj; exact hj
    have nb : j<native.val.length := by rw [native.property]; exact hjN
    have ev := earlyValues ⟨j,hjN⟩
    have nv := nativeValues.2 j hjN
    have nc : FIo_WideValues.Canon native.val[j] := nativeValues.1 _ (List.getElem_mem nb)
    have ec : FIo_WideValues.Canon (FIo_Install.toE early.val[j]) := canonical_of_early _ ev.1
    have nv' : AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide native.val[j]) =
      AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide (FIo_Install.toE p.gamma))^j := by
     have h := nv
     first
     | (simp only [FIp_ArrayValue.value,List.getElem?_eq_getElem nb] at h; exact h)
     | (rw [FIp_ArrayValue.value,List.getElem?_eq_getElem nb] at h; exact h)
    have decoded :
      AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide (FIo_Install.toE early.val[j])) =
      AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide native.val[j]) := by
     rw [nv']
     first
     | exact ev.2
     | (rw [decode_link,decode_link]; exact ev.2)
    have eqn := identify _ _ ec nc decoded
    have back := congrArg FIo_Install.fromE eqn
    simp only [FIo_Install.from_to] at back
    rw [back]
    first
    | simp only [FIp_DotsAdapter.fromArray,List.getElem_map]
    | simp [FIp_DotsAdapter.fromArray]
 rw [sameOut] at same
 rw [← same]
 exact earlyCall

#print axioms identify
#print axioms canonical_gamma
#print axioms canonical_early
#print axioms canonical_of_early
#print axioms decode_link
#print axioms source
end AspisR1.NOF_PowersAssociation
end
