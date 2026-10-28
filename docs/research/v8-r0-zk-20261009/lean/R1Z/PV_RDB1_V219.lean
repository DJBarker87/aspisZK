import R1Z.PV_RDB1_PointerConstruct
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_V219

structure Four (T : Type) where
  a : T
  b : T
  c : T
  d : T

def sourceStep {X A : Type} (add : A → X → Result A) (s : Four A) (x : Four X) :
    Result (Four A) := do
  let a ← add s.a x.a
  let s1 := {s with a := a}
  let b ← add s1.b x.b
  let s2 := {s1 with b := b}
  let c ← add s2.c x.c
  let s3 := {s2 with c := c}
  let d ← add s3.d x.d
  ok {s3 with d := d}

def referenceStep {X A : Type} (add : A → X → Result A) (s : Four A) (x : Four X) :
    Result (Four A) := do
  let a ← add s.a x.a
  let b ← add s.b x.b
  let c ← add s.c x.c
  let d ← add s.d x.d
  ok ⟨a,b,c,d⟩

theorem step_complete {X A : Type} (add : A → X → Result A) (s : Four A) (x : Four X) :
    sourceStep add s x = referenceStep add s x := rfl

def indexedTail {Q : Type} (p : Array Q 28#usize) : List Q :=
  List.ofFn (fun i : Fin 27 => p.val[i.val+1]'(by
    have h := p.property
    change p.val.length=28 at h
    omega))

theorem tail_enumeration {Q : Type} (p : Array Q 28#usize) :
    p.val.drop 1 = indexedTail p := by
  have hp := p.property
  change p.val.length=28 at hp
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_drop]
  simp only [indexedTail,List.getElem?_ofFn]
  by_cases hi : i<27
  · have hb : 1+i<p.val.length := by omega
    simp only [dif_pos hi,List.getElem?_eq_getElem hb]
    congr 2
    omega
  · have hb : p.val.length ≤ 1+i := by omega
    simp only [dif_neg hi,List.getElem?_eq_none_iff.mpr hb]

def source {X A Q : Type} (initial : Four X → Result (Four A))
    (add : A → X → Result A) (finish : Four A → Result Q)
    (p : Array (Four X) 28#usize) : Result Q := do
  let first ← Array.index_usize p 0#usize
  let state ← initial first
  let state ← List.foldlM (sourceStep add) state (p.val.drop 1)
  finish state

def reference {X A Q : Type} (initial : Four X → Result (Four A))
    (add : A → X → Result A) (finish : Four A → Result Q)
    (p : Array (Four X) 28#usize) : Result Q := do
  let first ← Array.index_usize p 0#usize
  let state ← initial first
  let state ← List.foldlM (referenceStep add) state (indexedTail p)
  finish state

/-- The source's slice traversal equals the owned reference's 27 indexed
steps, with identical four-limb call order and complete Result propagation. -/
theorem complete {X A Q : Type} (initial : Four X → Result (Four A))
    (add : A → X → Result A) (finish : Four A → Result Q)
    (p : Array (Four X) 28#usize) :
    source initial add finish p = reference initial add finish p := by
  have hs : sourceStep add = referenceStep add := by funext s x; exact step_complete add s x
  simp only [source,reference,hs,tail_enumeration]

theorem all_bounds (i : Fin 27) : 0<28 ∧ 1≤28 ∧ i.val+1<28 := by omega

#print axioms step_complete
#print axioms tail_enumeration
#print axioms complete
#print axioms all_bounds
end R1Z.PV_RDB1_V219
