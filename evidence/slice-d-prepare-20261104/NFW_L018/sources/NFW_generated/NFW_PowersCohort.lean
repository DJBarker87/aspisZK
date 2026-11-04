import NFW_PowersInjective
import NFQ_STAGE2_IMPORT
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFW_PowersCohort
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NFW_PowersInjective
abbrev LE := AspisR1LoopPowers.field.WideExact
abbrev PE := AspisR1ClaimPreparedBridge.PE
def toLoop (x : NE) : LE :=
 ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
  ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
def fromLoop (x : LE) : NE :=
 ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
  ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
def toPublic (x : NE) : PE :=
 ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
  ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
def mapArray {A B : Type} {N : Usize} (f : A→B) (a : Array A N) : Array B N :=
 ⟨a.val.map f,by simpa only [List.length_map] using a.property⟩
theorem loop_roundtrip (x : LE) : toLoop (fromLoop x)=x := rfl
theorem loop_decode (x : LE) : decoded (fromLoop x)=AspisR1LoopPowers.decode x := rfl
/-- The actual emitted powers output equals the adopted early-return model,
by canonical coordinate injectivity. No XRn join or independently assumed
whole-output equation enters the proof. -/
theorem loop_model (N : Usize) (x : NE) (hx : canonE x) (out : Array NE N)
 (native : FIo_Native.weights.powers N x=ok out) :
 AspisR1LoopPowers.weights.early_powers N (toLoop x)=ok (mapArray toLoop out) := by
 have canonical : AspisR1LoopPowers.Canonical (toLoop x) := hx
 obtain ⟨model,call,values⟩ := AspisR1LoopPowers.early_powers_total_exact N (toLoop x) canonical
 have post := FIp_PowersValue.powers N x out hx native
 have same : model=mapArray toLoop out := by
  apply Subtype.ext
  apply List.ext_getElem
  · simpa only [List.length_map] using model.property.trans out.property.symm
  · intro i hi hj
    have bound : i<N.val := by rw [←model.property];exact hi
    have oi : i<out.val.length := by rw [out.property];exact bound
    obtain ⟨mc,mv⟩ := values ⟨i,bound⟩
    have nc := NFW_PowersDomain.canonical x hx out native _ (List.getElem_mem oi)
    have nv := post.2 i bound
    simp only [FIp_ArrayValue.value,List.getElem?_eq_getElem oi] at nv
    have value : decoded (fromLoop (model.val[i]'hi))=decoded (out.val[i]'oi) := by
     rw [loop_decode,mv]
     exact nv.symm
    have eq := injective (fromLoop (model.val[i]'hi)) (out.val[i]'oi) mc nc value
    have mapped := congrArg toLoop eq
    simpa only [loop_roundtrip,mapArray,List.getElem_map] using mapped
 rw [same] at call
 exact call
/-- Complete source-to-cohort powers equality at the same input/output. -/
theorem source (N : Usize) (x : NE) (hx : canonE x) :
 ∃ out, FIo_Native.weights.powers N x=ok out ∧
  AspisR1ClaimPreparedBridge.powersPublic N (toPublic x)=ok (mapArray toPublic out) ∧
  (∀ z∈out.val,canonE z) := by
 obtain ⟨out,native,_⟩ := NFW_LPi_PowersSource.source N x hx
 have model := loop_model N x hx out native
 refine ⟨out,native,?_,NFW_PowersDomain.canonical x hx out native⟩
 unfold AspisR1ClaimPreparedBridge.powersPublic AspisR1CurrentPreparedClaim.ClaimPowers.powers
 have input : AspisR1CurrentPreparedClaim.ClaimPowers.toPowers
  (AspisR1ClaimPreparedBridge.toClaimE (toPublic x))=toLoop x := rfl
 rw [input,model,bind_tc_ok]
 congr 1
 apply Subtype.ext
 simp only [mapArray,AspisR1ClaimPreparedBridge.mapArray,
  AspisR1CurrentPreparedClaim.ClaimPowers.mapArray,List.map_map]
 rfl
#print axioms loop_roundtrip
#print axioms loop_decode
#print axioms loop_model
#print axioms source
end AspisR1.NFW_PowersCohort
