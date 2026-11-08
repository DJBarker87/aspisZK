import NNU_CommonSelected
import FIp_PowersValue
import SAQ_Inverse
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNY_PowersAssociation
open Aeneas Aeneas.Std Result VTop_Stages

-- Coordinate proof follows identify; avoid its unrelated fixture closure.
private theorem identify (x y : FIo_Install.NE) (hx : FIo_WideValues.Canon x)
 (hy : FIo_WideValues.Canon y)
 (same : AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide x)=
   AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide y)) : x=y := by
 rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩
 rcases y with ⟨⟨⟨a1,b1⟩,⟨c1,d1⟩⟩,⟨⟨e1,f1⟩,⟨g1,h1⟩⟩⟩
 congr 3
 · exact SAQ_Inverse.canonical_injective _ _ hx.1.1.1 hy.1.1.1 (congrArg (fun z => z.re.re.re) same)
 · exact SAQ_Inverse.canonical_injective _ _ hx.1.1.2 hy.1.1.2 (congrArg (fun z => z.re.re.im) same)
 · exact SAQ_Inverse.canonical_injective _ _ hx.1.2.1 hy.1.2.1 (congrArg (fun z => z.re.im.re) same)
 · exact SAQ_Inverse.canonical_injective _ _ hx.1.2.2 hy.1.2.2 (congrArg (fun z => z.re.im.im) same)
 · exact SAQ_Inverse.canonical_injective _ _ hx.2.1.1 hy.2.1.1 (congrArg (fun z => z.im.re.re) same)
 · exact SAQ_Inverse.canonical_injective _ _ hx.2.1.2 hy.2.1.2 (congrArg (fun z => z.im.re.im) same)
 · exact SAQ_Inverse.canonical_injective _ _ hx.2.2.1 hy.2.2.1 (congrArg (fun z => z.im.im.re) same)
 · exact SAQ_Inverse.canonical_injective _ _ hx.2.2.2 hy.2.2.2 (congrArg (fun z => z.im.im.im) same)
#print axioms identify

theorem source (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NID_ResumeFields.Domain p a)
 (out : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (called : NHT_PacketOps.powers 29#usize p.gamma=ok out) :
 Tx2N_Powers.powers 29#usize p.gamma=ok out := by
 have canonical : FIo_WideValues.Canon (FIo_Install.toE p.gamma) := by
  rcases domain.gamma with ⟨⟨a,b,c,d⟩,⟨e,f,g,h⟩⟩
  exact ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩
 have earlyCanonical : AspisR1LoopPowers.Canonical (Tx2N_Powers.toPowers p.gamma) := by
  exact domain.gamma
 obtain ⟨native,nativeCall,associated⟩ := Port3_PushFrame.bind_success _ _ _ called
 have sameOut : FIp_DotsAdapter.fromArray native=out := Result.ok.inj associated
 obtain ⟨early,earlyCall,earlyValues⟩ := Tx2N_Powers.total_exact 29#usize p.gamma earlyCanonical
 have nativeValues := FIp_PowersValue.powers 29#usize _ native canonical nativeCall
 have same : early=FIp_DotsAdapter.fromArray native := by
  apply Subtype.ext
  apply List.ext_getElem
  · exact early.property.trans (by simp only [FIp_DotsAdapter.fromArray,List.length_map,native.property])
  · intro j hj hk
    have bound : j<29 := by rw [early.property] at hj;exact hj
    have nv := nativeValues.2 j bound
    have ev := earlyValues ⟨j,bound⟩
    have nb : j<native.val.length := by rw [native.property];exact bound
    have nc := nativeValues.1 _ (List.getElem_mem nb)
    have ec : FIo_WideValues.Canon (FIo_Install.toE early.val[j]) := by
     exact ev.1
    have decoded : AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide (FIo_Install.toE early.val[j])) =
      AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide native.val[j]) := by
     change AspisR1LoopPowers.decode (Tx2N_Powers.toPowers early.val[j]) = _
     rw [ev.2]
     have ng : AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide (FIo_Install.toE p.gamma)) =
       AspisR1LoopPowers.decode (Tx2N_Powers.toPowers p.gamma) := rfl
     simpa only [FIp_ArrayValue.value,List.getElem?_eq_getElem nb,ng] using nv.symm
    have eqn := identify _ _ ec nc decoded
    have back := congrArg FIo_Install.fromE eqn
    simpa only [FIo_Install.from_to,FIp_DotsAdapter.fromArray,List.getElem_map] using back
 rw [sameOut] at same
 exact same ▸ earlyCall
#print axioms source
end AspisR1.NNY_PowersAssociation
end
