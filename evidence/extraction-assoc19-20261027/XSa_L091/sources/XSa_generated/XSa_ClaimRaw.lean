import XSa_PointList
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport XSa_DotRun
set_option autoImplicit false
namespace XSa_ClaimRaw
abbrev Seven := XRy_ClaimSumStep.Seven

def outcome : Option C.E → core.result.Result C.E C.Err
 | none => .Err .Parse
 | some out => .Ok out

theorem factor {H : Type} (D : C.D H) (sem : C.Sem H) (s : Slice U8)
 (inactive : C.E) (g : Coeff) (kappa : C.E) (k : Seven)
 (hp : XRn_Join_powers kappa 7 XRy_Powers.one=ok k.val) :
 XRo_Join_PreparedBoundaries.cachedClaim D sem s inactive g kappa =
 mapR outcome (do
   let xs ← XSa_OptionFold.run (XSa_PointList.step sem s g) (List.range 6) []
   XSa_PointList.finish inactive k xs) := by
 unfold XRo_Join_PreparedBoundaries.cachedClaim _root_.verifier.prepared_claim
 simp only [_root_.aspis_core.field.wide_exact.WideExact.ONE,
   _root_.aspis_core.field.wide_exact.WideExact.ZERO,bind_tc_ok]
 change mapR (inner id ce) (do
   let powers ← XRn_Join_powers kappa 7 XRy_Powers.one
   let parts ← (List.range 6).foldlM (XSa_OptionFold.absorb (XSa_PointList.step sem s g)) (some [])
   match parts with
   | none => ok (core.result.Result.Err XRn_Join_Release.verifier.Error.Parse)
   | some parts => do
     let result ← (powers.zip (inactive::parts)).foldlM XSa_ClaimPairs.addTerm XRy_Powers.zero
     ok (.Ok result)) = _
 rw [hp,bind_tc_ok,←XSa_OptionFold.same]
 simp only [mapR_bind]
 apply congrArg (fun f => XSa_OptionFold.run (XSa_PointList.step sem s g) (List.range 6) [] >>= f)
 intro xs
 cases xs with
 | none => rfl
 | some parts =>
   unfold XSa_PointList.finish
   simp only [mapR_bind,bind_tc_ok]
   rfl

#print axioms factor
end XSa_ClaimRaw
