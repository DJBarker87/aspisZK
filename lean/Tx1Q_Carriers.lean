import RowShape_InstalledSlots
import Port3_QueryStage
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Tx1Q_Carriers
namespace C
open AspisR1CurrentCaller
abbrev K := aspis_core.field.QM31
abbrev E := aspis_core.field.wide_exact.WideExact
abbrev P := verifier.Prepared
abbrev A := verifier.Accumulator
abbrev B := verifier.BatchedWeights
abbrev G := verifier.QueryGeometry
end C
namespace S
open AspisR1Stage2
abbrev K := aspis_core.field.QM31
abbrev E := aspis_core.field.wide_exact.WideExact
abbrev P := verifier.Prepared
abbrev A := verifier.Accumulator
abbrev B := verifier.BatchedWeights
abbrev G := verifier.QueryGeometry
end S

def k (x : C.K) : S.K := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def unK (x : S.K) : C.K := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def e (x : C.E) : S.E := ⟨k x.c0,k x.c1⟩
def unE (x : S.E) : C.E := ⟨unK x.c0,unK x.c1⟩
def arr {A B : Type} {n : Usize} (f : A → B) (x : Array A n) : Array B n :=
  ⟨x.val.map f,by simpa using x.property⟩
def vec {A B : Type} (f : A → B) (x : alloc.vec.Vec A) : alloc.vec.Vec B :=
  ⟨x.val.map f,by simpa using x.property⟩
def slice {A B : Type} (f : A → B) (x : Slice A) : Slice B :=
  ⟨x.val.map f,by simpa using x.property⟩
def variant : AspisR1CurrentCaller.transport.Variant → AspisR1Stage2.transport.Variant
  | .S1 => .S1 | .S2 => .S2 | .D => .D

def prepared (p : C.P) : S.P :=
  ⟨variant p.variant,p.roots,e p.gamma,e p.kappa,arr e p.alpha,k p.rho,p.queries,
    arr k p.semantic_alpha,arr (fun z => ⟨k z.x,k z.y⟩) p.z,e p.claim,p.state⟩
def accumulator (a : C.A) : S.A := ⟨vec k a.weights,e a.rhs,k a.power,a.next⟩
def unAccumulator (a : S.A) : C.A := ⟨vec unK a.weights,unE a.rhs,unK a.power,a.next⟩
def pending (b : C.B) : S.B := ⟨b.raw,b.terms⟩
def unPending (b : S.B) : C.B := ⟨b.raw,b.terms⟩
def geometry (g : C.G) : S.G := ⟨g.start,g.inverses,g.line_z⟩
def phase : AspisR1Stage2.verifier.Phase → AspisR1CurrentCaller.verifier.Phase
  | .Parsed  => .Parsed 
  | .Semantic  => .Semantic 
  | .SemanticPart p => .SemanticPart p
  | .Prepare  => .Prepare 
  | .CheckpointRead  => .CheckpointRead 
  | .Merkle n => .Merkle n
  | .Query n => .Query n
  | .QueryPart n p => .QueryPart n p
  | .CheckpointWrite  => .CheckpointWrite 
  | .Relation  => .Relation 
  | .Final  => .Final 
def observer (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit)) :
    Option (AspisR1Stage2.verifier.Phase → Result Unit) := obs.map (fun f => fun p => f (phase p))
def error : AspisR1Stage2.verifier.Error → AspisR1CurrentCaller.verifier.Error
  | .Parse => .Parse
  | .Semantic => .Semantic
  | .Transcript => .Transcript
  | .Relation => .Relation
  | .Merkle => .Merkle
  | .Query => .Query
  | .Checkpoint => .Checkpoint
  | .Allocation => .Allocation

@[simp] theorem k_unK (x : S.K) : k (unK x) = x := by cases x; rfl
@[simp] theorem unK_k (x : C.K) : unK (k x) = x := by cases x; rfl
@[simp] theorem e_unE (x : S.E) : e (unE x) = x := by
  cases x
  simp only [e,unE,k_unK]
@[simp] theorem unE_e (x : C.E) : unE (e x) = x := by
  cases x
  simp only [e,unE,unK_k]
@[simp] theorem accumulator_roundtrip (a : S.A) : accumulator (unAccumulator a) = a := by
  cases a
  simp [accumulator,unAccumulator,vec,List.map_map,Function.comp_def]
@[simp] theorem current_roundtrip (a : C.A) : unAccumulator (accumulator a) = a := by
  cases a
  simp [accumulator,unAccumulator,vec,List.map_map,Function.comp_def]
@[simp] theorem pending_roundtrip (b : S.B) : pending (unPending b) = b := by cases b; rfl
@[simp] theorem current_pending_roundtrip (b : C.B) : unPending (pending b) = b := by cases b; rfl

theorem materialize (a : C.A) (s : Slice C.K) :
    accumulator {a with weights := ⟨s.val,s.property⟩} =
      {accumulator a with weights := ⟨(slice k s).val,(slice k s).property⟩} := rfl

#print axioms k_unK
#print axioms unK_k
#print axioms e_unE
#print axioms unE_e
#print axioms accumulator_roundtrip
#print axioms current_roundtrip
#print axioms pending_roundtrip
#print axioms current_pending_roundtrip
#print axioms materialize
end AspisR1.Tx1Q_Carriers
end
