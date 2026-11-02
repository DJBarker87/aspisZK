import NBO_TailDomain
open Aeneas Aeneas.Std Result
set_option autoImplicit false
noncomputable section
namespace NBO_QueryDomains
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
open Port3_PushFrame (bind_success)
open NBO_TailDomain (WideCanonical)
def AllWide {n : Usize} (v : Array Stage2E n) : Prop :=
 ∀ x ∈ v.val, WideCanonical x
def AllBase {n : Usize} (v : Array U32 n) : Prop :=
 ∀ x ∈ v.val, x.val<2147483647
structure GeometryDomain (geometry : verifier.QueryGeometry) : Prop where
 start : geometry.start=0#usize
 inverseLength : geometry.inverses.val.length=10
 lineLength : geometry.line_z.val.length=10
 inverse : ∀ row ∈ geometry.inverses.val, AllBase row
 line : ∀ x ∈ geometry.line_z.val, x.val<2147483647
/-- Lower decoder, standard-array, geometry lookup and field result laws.
These are exact named dependencies, not native-query or accepted-result laws.
The geometry producer and prepared alpha domain remain separate lower rows. -/
structure Lower (ops : Ops) : Prop where
 decode : ∀ bytes i out, ops.op21 bytes i=ok out → WideCanonical out
 fromFn : ∀ {T F : Type} (n : Usize) (dict : core.ops.function.FnMut F Usize T)
   (initial : F) (out : Array T n) (property : T → Prop),
   (∀ state i x next, dict.call_mut state i=ok (x,next) → property x) →
   ops.op0 n dict initial=ok out → ∀ x ∈ out.val, property x
 inverse : ∀ geometry i inverse, GeometryDomain geometry → i.val<10 →
   ops.op18 geometry i=ok inverse → AllBase inverse
 line : ∀ alpha values inverse out, WideCanonical alpha → AllWide values →
   AllBase inverse → ops.op16 alpha values inverse=ok out → WideCanonical out
/-- Success of the SAME decoder closure derives its canonical reply, even
when the input bytes are malformed: failure supplies no successful reply. -/
theorem closure (ops : Ops) (lower : Lower ops)
 (c : verifier.candidate.query_values.closure) (i : Usize)
 (value : Stage2E) (next : verifier.candidate.query_values.closure)
 (run : verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
   ops c i=ok (value,next)) : WideCanonical value := by
 unfold verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut at run
 obtain ⟨bytes,hbytes,run⟩ := bind_success _ _ _ run
 obtain ⟨decoded,hdecoded,run⟩ := bind_success _ _ _ run
 cases Result.ok.inj run
 exact lower.decode bytes i value hdecoded
/-- Values and inverse are the exact successful prefix returns. Their
canonicality is a conclusion, rather than a separately selected witness. -/
theorem front (ops : Ops) (lower : Lower ops) (proof : Slice U8)
 (p : verifier.Prepared) (next : Usize) (g : Array Stage2E 29#usize)
 (geometry : verifier.QueryGeometry) (domain : GeometryDomain geometry)
 (active : next.val<10) (circle : Stage2E) (values : Array Stage2E 4#usize)
 (inverse : Array U32 5#usize)
 (run : NBO_QueryFactor.front ops proof p next g geometry=ok (.Ok (circle,values,inverse))) :
 AllWide values ∧ AllBase inverse := by
 unfold NBO_QueryFactor.front at run
 iterate 4 obtain ⟨x,hx,run⟩ := bind_success _ _ _ run
 iterate 15 obtain ⟨x,hx,run⟩ := bind_success _ _ _ run
 obtain ⟨inv,hinv,run⟩ := bind_success _ _ _ run
 iterate 4 obtain ⟨x,hx,run⟩ := bind_success _ _ _ run
 obtain ⟨vals,hvals,run⟩ := bind_success _ _ _ run
 iterate 3 obtain ⟨x,hx,run⟩ := bind_success _ _ _ run
 split at run
 · cases run
 · cases Result.ok.inj run
   exact ⟨lower.fromFn _ _ _ values WideCanonical (closure ops lower) hvals,
     lower.inverse geometry next inverse domain active hinv⟩
#print axioms closure
#print axioms front
end NBO_QueryDomains
end
