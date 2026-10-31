import NEB_WordRefs
set_option autoImplicit false
namespace NEB_ArrayRefs
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

def wordsC (x : NC) : Array U32 2#usize := Array.make 2#usize [x.a,x.b]
def wordsQ (x : NQ) : Array U32 4#usize :=
  Array.make 4#usize [x.c0.a,x.c0.b,x.c1.a,x.c1.b]
def wordsE (x : NE) : Array U32 8#usize :=
  Array.make 8#usize [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,
    x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]

theorem cm_add (x y : NC) : NEB_AdditiveRef.add2 (wordsC x) (wordsC y) =
    (do let z ← FIo_Native.aspis_core.field.CM31.add x y;ok (wordsC z)) := by
  simp [NEB_AdditiveRef.add2,wordsC,Array.index_usize,Array.make,
    NEB_WordRefs.add,FIo_Native.aspis_core.field.CM31.add,bind_assoc_eq]

theorem cm_sub (x y : NC) : NEB_AdditiveRef.sub2 (wordsC x) (wordsC y) =
    (do let z ← FIo_Native.aspis_core.field.CM31.sub x y;ok (wordsC z)) := by
  simp [NEB_AdditiveRef.sub2,wordsC,Array.index_usize,Array.make,
    NEB_WordRefs.sub,FIo_Native.aspis_core.field.CM31.sub,bind_assoc_eq]

theorem qm_add (x y : NQ) : NEB_AdditiveRef.add4 (wordsQ x) (wordsQ y) =
    (do let z ← FIo_Native.aspis_core.field.QM31.add x y;ok (wordsQ z)) := by
  simp [NEB_AdditiveRef.add4,wordsQ,Array.index_usize,Array.make,
    NEB_WordRefs.add,FIo_Native.aspis_core.field.QM31.add,
    FIo_Native.aspis_core.field.CM31.add,bind_assoc_eq]

theorem qm_sub (x y : NQ) : NEB_AdditiveRef.sub4 (wordsQ x) (wordsQ y) =
    (do let z ← FIo_Native.aspis_core.field.QM31.sub x y;ok (wordsQ z)) := by
  simp [NEB_AdditiveRef.sub4,wordsQ,Array.index_usize,Array.make,
    NEB_WordRefs.sub,FIo_Native.aspis_core.field.QM31.sub,
    FIo_Native.aspis_core.field.CM31.sub,bind_assoc_eq]

theorem wide_add (x y : NE) : NEB_AdditiveRef.add8 (wordsE x) (wordsE y) =
    (do let z ← FIo_Native.aspis_core.field.wide_exact.WideExact.add x y;ok (wordsE z)) := by
  simp [NEB_AdditiveRef.add8,wordsE,Array.index_usize,Array.make,
    NEB_WordRefs.add,FIo_Native.aspis_core.field.wide_exact.WideExact.add,
    FIo_Native.aspis_core.field.QM31.add,FIo_Native.aspis_core.field.CM31.add,bind_assoc_eq]

theorem cm_injective : Function.Injective wordsC := by
  intro x y h
  rcases x with ⟨a,b⟩
  rcases y with ⟨c,d⟩
  have values := congrArg (fun (a : Array U32 2#usize) => a.val) h
  simp [wordsC,Array.make] at values
  rcases values with ⟨rfl,rfl⟩
  rfl

theorem qm_injective : Function.Injective wordsQ := by
  intro x y h
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  rcases y with ⟨⟨e,f⟩,⟨g,k⟩⟩
  have values := congrArg (fun (a : Array U32 4#usize) => a.val) h
  simp [wordsQ,Array.make] at values
  rcases values with ⟨rfl,rfl,rfl,rfl⟩
  rfl

theorem wide_injective : Function.Injective wordsE := by
  intro x y h
  rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,k⟩⟩⟩
  rcases y with ⟨⟨⟨l,m⟩,⟨n,o⟩⟩,⟨⟨p,q⟩,⟨r,s⟩⟩⟩
  have values := congrArg (fun (a : Array U32 8#usize) => a.val) h
  simp [wordsE,Array.make] at values
  rcases values with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  rfl

#print axioms cm_add
#print axioms cm_sub
#print axioms qm_add
#print axioms qm_sub
#print axioms wide_add
#print axioms cm_injective
#print axioms qm_injective
#print axioms wide_injective
end NEB_ArrayRefs
