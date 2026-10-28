import PV_B3P_NativeFieldsVec226
namespace PV_B3P_NativeSteps226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_RustResult PV_B3P_ByteLayout226V3
set_option autoImplicit false
abbrev E := aspis_core.state_only_prefix.r0.Error
inductive Step where
  | push : U8 → Step
  | bytes : Slice U8 → Step
  | fields : List U32 → Step

def width : Step → Nat
  | .push _ => 1
  | .bytes s => s.val.length
  | .fields xs => 4*xs.length

def budget : List Step → Nat
  | [] => 0
  | x::xs => width x + budget xs

def runVec (out : alloc.vec.Vec U8) : List Step → Result (core.result.Result (alloc.vec.Vec U8) E)
  | [] => .ok (.Ok out)
  | .push b::xs => do let out' ← alloc.vec.Vec.push out b; runVec out' xs
  | .bytes s::xs => do
      let out' ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s
      runVec out' xs
  | .fields fs::xs => bindR (PV_B3P_NativeFieldsVec226.fieldsVec out fs) (fun out' => runVec out' xs)

def runList (out : List U8) : List Step → Result (core.result.Result (List U8) E)
  | [] => .ok (.Ok out)
  | .push b::xs => runList (out++[b]) xs
  | .bytes s::xs => runList (out++s.val) xs
  | .fields fs::xs => bindR (PV_B3P_AppendFields226.nativeFields out fs) (fun out' => runList out' xs)

set_option backward.isDefEq.respectTransparency false in
theorem complete_result (out : alloc.vec.Vec U8) (xs : List Step)
    (hb : out.val.length + budget xs ≤ Usize.max) :
    mapR (fun v : alloc.vec.Vec U8 => v.val) (runVec out xs) = runList out.val xs := by
  induction xs generalizing out with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | push b =>
      obtain ⟨out',hout',hval⟩ := PV_B3P_VecValue226.push_value out b (by
        simp only [budget,width] at hb
        omega)
      have hb' : out'.val.length + budget xs ≤ Usize.max := by
        rw [hval,List.length_append]
        simp only [budget,width,List.length_cons,List.length_nil] at hb ⊢
        omega
      simp only [runVec,hout',bind_tc_ok,runList]
      rw [ih out' hb',hval]
    | bytes s =>
      obtain ⟨out',hout',hval⟩ := PV_B3P_VecValue226.u8_extend out s (by
        simp only [budget,width] at hb
        omega)
      have hb' : out'.val.length + budget xs ≤ Usize.max := by
        rw [hval,List.length_append]
        simp only [budget,width] at hb
        omega
      simp only [runVec,hout',bind_tc_ok,runList]
      rw [ih out' hb',hval]
    | fields fs =>
      have hm := PV_B3P_NativeFieldsVec226.complete_result out fs (by
        simp only [budget,width] at hb
        omega)
      generalize hx : PV_B3P_NativeFieldsVec226.fieldsVec out fs = r at hm ⊢
      cases r with
      | fail e =>
        rw [PV_B3P_AppendFields226.native_fields_complete] at hm
        split at hm <;> cases hm
      | div =>
        rw [PV_B3P_AppendFields226.native_fields_complete] at hm
        split at hm <;> cases hm
      | ok inner =>
        cases inner with
        | Err e =>
          simp only [mapR,bindR] at hm
          simp only [runVec,hx,bindR,mapR,← hm,runList]
        | Ok out' =>
          simp only [mapR,bindR] at hm
          have hval : out'.val = out.val ++ fields fs := by
            rw [PV_B3P_AppendFields226.native_fields_complete] at hm
            split at hm
            · exact core.result.Result.Ok.inj (Result.ok.inj hm)
            · cases hm
          have hb' : out'.val.length + budget xs ≤ Usize.max := by
            rw [hval,List.length_append,fields_length]
            simp only [budget,width] at hb
            omega
          simp only [runVec,hx,bindR,runList,← hm]
          exact ih out' hb'

#print axioms complete_result
end PV_B3P_NativeSteps226
