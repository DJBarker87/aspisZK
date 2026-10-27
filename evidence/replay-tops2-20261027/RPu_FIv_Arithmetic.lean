import RPu_FIq_Native02
import ExtractedMaskQM31Exact
import ExtractedMaskPreparedMul
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_Map
open Aeneas Aeneas.Std Result
def map {A B : Type} (f : A → B) : Result A → Result B
  | .ok x => .ok (f x) | .fail e => .fail e | .div => .div
theorem map_bind {A B C : Type} (f : B → C) (x : Result A) (k : A → Result B) :
    map f (do let v ← x; k v) = (do let v ← x; map f (k v)) := by
  cases x <;> rfl
theorem map_ok {A B : Type} (f : A → B) (x : A) : map f (.ok x)=.ok (f x) := rfl
theorem bind_success {A B : Type} (a : Result A) (f : A → Result B) (v : B)
    (h : (a >>= f)=ok v) : ∃ x,a=ok x ∧ f x=ok v := by
  cases a with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => cases h
  | div => cases h
#print axioms map_bind
#print axioms map_ok
#print axioms bind_success
end AspisR1.FIv_Map
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_NativeArithmetic
open Aeneas Aeneas.Std Result
open FIv_Map (map map_bind map_ok)
abbrev NQ := FIq_Native.field.QM31
abbrev NC := FIq_Native.field.CM31
abbrev PQ := AspisR1SelectedMaskProbe.field.QM31
abbrev PC := AspisR1SelectedMaskProbe.field.CM31

def cm (x : NC) : PC := ⟨x.a,x.b⟩
def qm (x : NQ) : PQ := ⟨cm x.c0,cm x.c1⟩

theorem bind_map {A B C : Type} (f : A → B) (m : Result A) (k : B → Result C) :
    (do let x←map f m;k x)=(do let x←m;k (f x)) := by
  cases m <;> rfl

theorem m31_add (x y : U32) : FIq_Native.field.M31.add x y=
    AspisR1SelectedMaskProbe.field.M31.add x y := by
  simp only [FIq_Native.field.M31.add,AspisR1SelectedMaskProbe.field.M31.add,
    FIq_Native.field.P,AspisR1SelectedMaskProbe.field.P]

theorem m31_sub (x y : U32) : FIq_Native.field.M31.sub x y=
    AspisR1SelectedMaskProbe.field.M31.sub x y := by
  simp only [FIq_Native.field.M31.sub,AspisR1SelectedMaskProbe.field.M31.sub,
    FIq_Native.field.P,AspisR1SelectedMaskProbe.field.P]

theorem m31_reduce (x : U64) : FIq_Native.field.M31.reduce_u64 x=
    AspisR1SelectedMaskProbe.field.M31.reduce_u64 x := by
  simp only [FIq_Native.field.M31.reduce_u64,AspisR1SelectedMaskProbe.field.M31.reduce_u64,
    FIq_Native.field.reduce_u64,AspisR1SelectedMaskProbe.field.reduce_u64,
    FIq_Native.field.P,AspisR1SelectedMaskProbe.field.P]

theorem m31_mul (x y : U32) : FIq_Native.field.M31.mul x y=
    AspisR1SelectedMaskProbe.field.M31.mul x y := by
  simp only [FIq_Native.field.M31.mul,AspisR1SelectedMaskProbe.field.M31.mul,
    FIq_Native.field.reduce_u64,AspisR1SelectedMaskProbe.field.reduce_u64,
    FIq_Native.field.P,AspisR1SelectedMaskProbe.field.P]

#print axioms bind_map
#print axioms m31_add
#print axioms m31_sub
#print axioms m31_reduce
#print axioms m31_mul
end AspisR1.FIv_NativeArithmetic
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_NativeCM
open Aeneas Aeneas.Std Result
open FIv_Map (map map_bind map_ok)
open FIv_NativeArithmetic

theorem add (x y : NC) : map cm (FIq_Native.field.CM31.add x y)=
    AspisR1SelectedMaskProbe.field.CM31.add (cm x) (cm y) := by
  simp only [FIq_Native.field.CM31.add,AspisR1SelectedMaskProbe.field.CM31.add,
    cm,map_bind,map_ok,m31_add]

theorem sub (x y : NC) : map cm (FIq_Native.field.CM31.sub x y)=
    AspisR1SelectedMaskProbe.field.CM31.sub (cm x) (cm y) := by
  simp only [FIq_Native.field.CM31.sub,AspisR1SelectedMaskProbe.field.CM31.sub,
    cm,map_bind,map_ok,m31_sub]

theorem mul (x y : NC) : map cm (FIq_Native.field.CM31.mul x y)=
    AspisR1SelectedMaskProbe.field.CM31.mul (cm x) (cm y) := by
  simp only [FIq_Native.field.CM31.mul,AspisR1SelectedMaskProbe.field.CM31.mul,
    cm,map_bind,map_ok,m31_mul,m31_sub,m31_reduce]

theorem by_r (x : NC) : map cm (FIq_Native.field.mul_by_r x)=
    AspisR1SelectedMaskProbe.field.mul_by_r (cm x) := by
  simp only [FIq_Native.field.mul_by_r,AspisR1SelectedMaskProbe.field.mul_by_r,
    FIq_Native.field.M31.double,AspisR1SelectedMaskProbe.field.M31.double,
    cm,map_bind,map_ok,m31_add,m31_sub]

#print axioms add
#print axioms sub
#print axioms mul
#print axioms by_r
end AspisR1.FIv_NativeCM
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_NativeQM
open Aeneas Aeneas.Std Result
open FIv_Map (map map_bind map_ok)
open FIv_NativeArithmetic

theorem add (x y : NQ) : map qm (FIq_Native.field.QM31.add x y)=
    AspisR1SelectedMaskProbe.field.QM31.add (qm x) (qm y) := by
  simp only [FIq_Native.field.QM31.add,AspisR1SelectedMaskProbe.field.QM31.add,qm,
    ← FIv_NativeCM.add,bind_map,map_bind,map_ok]

theorem mul (x y : NQ) : map qm (FIq_Native.field.QM31.mul x y)=
    AspisR1SelectedMaskProbe.field.QM31.mul (qm x) (qm y) := by
  simp only [FIq_Native.field.QM31.mul,AspisR1SelectedMaskProbe.field.QM31.mul,qm,
    ← FIv_NativeCM.mul,← FIv_NativeCM.add,← FIv_NativeCM.sub,← FIv_NativeCM.by_r,
    bind_map,map_bind,map_ok]

#print axioms add
#print axioms mul
end AspisR1.FIv_NativeQM
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_NativeValue
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic
open FIv_Map (map map_ok)
abbrev K := ExtractedMaskQM31Exact.QM31Exact
abbrev Canon (x : NQ) := ExtractedMaskQM31Exact.CurrentCanonicalQM (qm x)
abbrev decode (x : NQ) : K := ExtractedMaskQM31Exact.decode (qm x)

theorem add (x y z : NQ) (hx : Canon x) (hy : Canon y)
    (run : FIq_Native.field.QM31.add x y=ok z) :
    Canon z ∧ decode z=decode x+decode y := by
  obtain ⟨r,returned,canon,value⟩ := ExtractedMaskQM31Exact.current_qm_add_exact (qm x) (qm y) hx hy
  have mapped := FIv_NativeQM.add x y
  rw [run,map_ok,returned] at mapped
  have same := Result.ok.inj mapped
  rw [← same] at canon value
  exact ⟨canon,value⟩

theorem mul (x y z : NQ) (hx : Canon x) (hy : Canon y)
    (run : FIq_Native.field.QM31.mul x y=ok z) :
    Canon z ∧ decode z=decode x*decode y := by
  obtain ⟨r,returned,canon,value⟩ := ExtractedMaskQM31Exact.current_qm_mul_exact (qm x) (qm y) hx hy
  have mapped := FIv_NativeQM.mul x y
  rw [run,map_ok,returned] at mapped
  have same := Result.ok.inj mapped
  rw [← same] at canon value
  exact ⟨canon,value⟩

theorem zero : Canon FIq_Native.field.QM31.ZERO ∧ decode FIq_Native.field.QM31.ZERO=0 := by
  constructor
  · rw [FIq_Native.field.QM31.ZERO]
    exact ⟨⟨by decide,by decide⟩,⟨by decide,by decide⟩⟩
  · simp only [FIq_Native.field.QM31.ZERO,decode,ExtractedMaskQM31Exact.decode,qm,cm]
    rfl

theorem one : Canon FIq_Native.field.QM31.ONE ∧ decode FIq_Native.field.QM31.ONE=1 := by
  constructor
  · rw [FIq_Native.field.QM31.ONE]
    exact ⟨⟨by decide,by decide⟩,⟨by decide,by decide⟩⟩
  · simp only [FIq_Native.field.QM31.ONE,decode,ExtractedMaskQM31Exact.decode,qm,cm]
    rfl

#print axioms add
#print axioms mul
#print axioms zero
#print axioms one
end AspisR1.FIv_NativeValue
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_PreparedNew
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic
open FIv_Map (map map_bind map_ok)
abbrev NP := FIq_Native.field.PreparedQm31Multiplier
abbrev PP := AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier
def prepared (p : NP) : PP := ⟨p.components⟩
theorem component (x : NC) :
    FIq_Native.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call () x =
    AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call () (cm x) := by
  simp only [FIq_Native.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call,
    AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call,
    cm,m31_add]
theorem mapped (x : NQ) : map prepared (FIq_Native.field.PreparedQm31Multiplier.new x)=
    AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.new (qm x) := by
  simp only [FIq_Native.field.PreparedQm31Multiplier.new,
    AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.new,prepared,qm,
    map_bind,map_ok,component,← FIv_NativeCM.add,bind_map]
theorem valid (x : NQ) (p : NP) (hx : FIv_NativeValue.Canon x)
    (run : FIq_Native.field.PreparedQm31Multiplier.new x=ok p) :
    ExtractedMaskPreparedState.PreparedFor (prepared p) (qm x) := by
  obtain ⟨p',hp,hvalid⟩ := ExtractedMaskPreparedState.current_prepared_new (qm x) hx
  have same := mapped x
  rw [run,map_ok,hp] at same
  exact Result.ok.inj same ▸ hvalid
#print axioms component
#print axioms mapped
#print axioms valid
end AspisR1.FIv_PreparedNew
end
