import FJm_LibraPairTrace
import FJm_LibraInitialSlot
import FJg_SharedProvenance
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_PairTrace
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NQ NE)
open AspisR1Stage2 AspisR1Stage2.Stage2Finish

/-- All cuts of one producing Pair. No final-array identity is inferred from an equal sum. -/
structure Trace [FIo_Native.Allocation] (w : FIo_Native.weights.Weights)
    (alpha : Slice NE) (f : Slice U8) (kappa out : NE) where
  scratch : alloc.vec.Vec NQ
  scratchOut : alloc.vec.Vec NQ
  a0 : NE
  a1 : NE
  ap0 : Array NE 4#usize
  ap1 : Array NE 4#usize
  commonPartials : Array NE 4#usize
  common : Array NQ 16#usize
  regularParts : Array NE 7#usize
  sharedParts : Array NE 7#usize
  lowParts : Array NE 7#usize
  parts : Array NE 7#usize
  k : Array NE 7#usize
  low : Array NE 16#usize
  inactive : NE
  libra : Array NE 4#usize
  regular : FIo_Native.weights.process_regular_kinds w true alpha f 2#usize 64#usize ap0 ap1 scratch
    (Array.repeat 7#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)=ok (.Ok (),scratchOut,regularParts)
  filled : FIo_Native.aspis_core.r0.heap.filled FIo_Native.aspis_core.field.QM31.Insts.CoreMarkerCopy
    64#usize FIo_Native.aspis_core.field.QM31.ZERO=ok (.Ok scratch)
  read0 : Slice.index_usize alpha 0#usize=ok a0
  powers0 : FIo_Native.weights.powers 4#usize a0=ok ap0
  read1 : Slice.index_usize alpha 1#usize=ok a1
  powers1 : FIo_Native.weights.powers 4#usize a1=ok ap1
  commonRun : FIo_Native.weights.Weights.pair_loop1 {start:=0#usize,«end»:=16#usize} w
    (Array.repeat 16#usize FIo_Native.aspis_core.field.QM31.ZERO)=ok (w,common)
  partialsRun : FIo_Native.weights.shared_partials f common=ok (.Ok commonPartials)
  sharedRun : FIo_Native.weights.shared_high commonPartials w ap0 ap1 regularParts=ok (.Ok (),sharedParts)
  lowRun : FIo_Native.weights.Weights.pair_loop15 {start:=0#usize,«end»:=16#usize} ap0 ap1
    (Array.repeat 16#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)=ok low
  inactiveRun : FIo_Native.weights.grouped_inactive_pair w f low=ok inactive
  inactiveWrite : Array.update sharedParts 0#usize inactive=ok lowParts
  libraRun : FIo_Native.weights.factored_s2_libra_weights ap0 ap1 w.extra=ok libra
  libraZero : lowParts.val[4]?=some FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO
  libraWrite : FIo_Native.weights.Weights.pair_loop16 {start:=0#usize,«end»:=4#usize} f lowParts libra=ok parts
  powersK : FIo_Native.weights.powers 7#usize kappa=ok k
  sum : FIo_Native.weights.Weights.pair_loop17 {start:=0#usize,«end»:=7#usize} parts k
    FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok out

theorem reached (r : NP6_StdModel.Reservation) (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (alpha : Slice E) (f : Slice U8) (kappa out : E)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (folds : Slice.len (FIo_Install.toSlice alpha)=2#usize) (len : f.val.length=2048)
    (run : FIo_Install.pair r w alpha f kappa=ok (.Ok out)) :
    ∃ nativeOut,FIo_Install.fromE nativeOut=out ∧
      Nonempty (@Trace (FIo_Install.allocation r) (FIo_Install.toWeights w)
        (FIo_Install.toSlice alpha) f (FIo_Install.toE kappa) nativeOut) := by
  letI := FIo_Install.allocation r
  obtain ⟨_,_,_,_,_,_,guard,rest⟩ := FJg_SharedProvenance.value r semAlpha z w alpha f kappa out hc hw folds run
  obtain ⟨nativeOut,hn,he⟩ := FIo_Install.reached r w alpha f kappa out run
  obtain ⟨n,scratch,scratchOut,a0,a1,ap0,ap1,nativeSelf,common,partials,
    before,highParts,lowParts,parts,k,low,inactive,libra,status,b,
    hregular,hnsize,hfilled,h0,hp0,h1,hp1,hcom,same,hpartial,hhigh,hstatus,hl,hi,hu,hvariant,hlibra,hlib,hk,hsum⟩ :=
    FJm_LibraPairTrace.reached (FIo_Install.toWeights w) (FIo_Install.toSlice alpha) f
      (FIo_Install.toE kappa) nativeOut folds guard hn
  subst nativeSelf
  subst status
  have : n=64#usize := by apply UScalar.eq_of_val_eq;rw [hnsize,len];rfl
  n64 : n=64#usize := by apply UScalar.eq_of_val_eq;rw [hnsize,len];rfl
  subst n
  obtain ⟨_,_,_,_,_,_,_,_,_,_,variant,_⟩ := FJc_InstalledParts.value .S2 semAlpha z w hw
  have : (FIo_Install.toWeights w).variant=.S2 := variant
  variantS2 : (FIo_Install.toWeights w).variant=.S2 := variant
  have : b=true := by
  eb : b=true := by
    rw [variantS2] at hvariant
    have normal : FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq .S2 .S2=ok true := by
      unfold FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq FIo_Native.transport.Variant.read_discriminant
      simp only [eq_self,decide_true]
    rw [normal] at hvariant
    exact (Result.ok.inj hvariant).symm
  have : FIo_Native.weights.factored_s2_libra_weights ap0 ap1 (FIo_Install.toWeights w).extra=ok libra := by
  actual : FIo_Native.weights.factored_s2_libra_weights ap0 ap1 (FIo_Install.toWeights w).extra=ok libra := by
    simpa only [eb,ite_true] using hlibra
  have := FJm_LibraInitialSlot.value (FIo_Install.toWeights w) (FIo_Install.toSlice alpha)
  initial := FJm_LibraInitialSlot.value (FIo_Install.toWeights w) (FIo_Install.toSlice alpha)
    f 2#usize 64#usize ap0 ap1 partials scratch scratchOut before highParts lowParts inactive hregular hhigh hu
  exact ⟨nativeOut,he,⟨⟨scratch,scratchOut,a0,a1,ap0,ap1,partials,common,before,highParts,lowParts,parts,k,
    low,inactive,libra,hregular,hfilled,h0,hp0,h1,hp1,hcom,hpartial,hhigh,hl,hi,hu,actual,initial,hlib,hk,hsum⟩⟩⟩

#print axioms reached
end AspisR1.FJr_PairTrace
end
