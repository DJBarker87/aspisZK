import R1Z.ProverCommitOpeningBytes49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OpeningStreamUnique69
open Aeneas Aeneas.Std ProverCommitPrimitive47 ProverCommitWideOps48

def unpack (s : Source) : Raw :=
  (⟨⟨s.c0.c0.a,s.c0.c0.b⟩,⟨s.c0.c1.a,s.c0.c1.b⟩⟩,
   ⟨⟨s.c1.c0.a,s.c1.c0.b⟩,⟨s.c1.c1.a,s.c1.c1.b⟩⟩)

theorem unpack_source (x : Raw) : unpack (source x)=x := by
  rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩
  rfl

theorem source_injective : Function.Injective source := by
  intro x y h
  simpa only [unpack_source] using congrArg unpack h

attribute [local irreducible] source List.ofFn

theorem stream (n : Nat) (x y : Nat → Raw)
    (hx : ∀ i,i<n → canonical (x i)) (hy : ∀ i,i<n → canonical (y i))
    (h : List.ofFn (fun i : Fin n => source (x i.val))=
      List.ofFn (fun i : Fin n => source (y i.val))) :
    ProverCommitOpeningBytes49.stream n x hx=ProverCommitOpeningBytes49.stream n y hy := by
  have point : ∀ i : Fin n,x i.val=y i.val := by
    intro i
    apply source_injective
    have cell := congrArg (fun xs : List Source => xs[i.val]?) h
    simpa only [List.getElem?_ofFn,i.isLt,↓reduceDIte,Option.some.injEq] using cell
  unfold ProverCommitOpeningBytes49.stream
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  exact congrArg (fun z : {r : Raw // canonical r} =>
    List.ofFn (ProverCommitWideBytes48.sourceCell z.val z.property))
    (Subtype.ext (point i))

#print axioms unpack
#print axioms unpack_source
#print axioms source_injective
#print axioms stream
end R1Z.PV_RunJoin_OpeningStreamUnique69
