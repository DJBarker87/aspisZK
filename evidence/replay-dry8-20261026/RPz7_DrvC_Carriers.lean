import RPz7_Tx1Q_Carriers
import RPz7_DrvI_Installation
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_Carriers
open Aeneas Aeneas.Std Result
open Tx1Q_Carriers

def unVariant : AspisR1Stage2.transport.Variant → AspisR1CurrentCaller.transport.Variant
  | .S1 => .S1 | .S2 => .S2 | .D => .D

def unPrepared (p : S.P) : C.P :=
  ⟨unVariant p.variant,p.roots,unE p.gamma,unE p.kappa,arr unE p.alpha,unK p.rho,p.queries,
    arr unK p.semantic_alpha,arr (fun z => ⟨unK z.x,unK z.y⟩) p.z,unE p.claim,p.state⟩

def unGeometry (g : S.G) : C.G := ⟨g.start,g.inverses,g.line_z⟩

def fromError : AspisR1CurrentCaller.verifier.Error → AspisR1Stage2.verifier.Error
  | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
  | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
  | .Checkpoint => .Checkpoint | .Allocation => .Allocation

@[simp] theorem variant_roundtrip (v : AspisR1Stage2.transport.Variant) :
    variant (unVariant v) = v := by cases v <;> rfl
@[simp] theorem current_variant_roundtrip (v : AspisR1CurrentCaller.transport.Variant) :
    unVariant (variant v) = v := by cases v <;> rfl
@[simp] theorem prepared_roundtrip (p : S.P) : prepared (unPrepared p) = p := by
  cases p
  simp only [unPrepared,prepared,variant_roundtrip,e_unE,k_unK,arr,List.map_map,Function.comp_def]
  congr <;> simp
@[simp] theorem current_prepared_roundtrip (p : C.P) : unPrepared (prepared p) = p := by
  cases p
  simp only [unPrepared,prepared,current_variant_roundtrip,unE_e,unK_k,arr,List.map_map,Function.comp_def]
  congr <;> simp
@[simp] theorem geometry_roundtrip (g : S.G) : geometry (unGeometry g) = g := by cases g; rfl
@[simp] theorem current_geometry_roundtrip (g : C.G) : unGeometry (geometry g) = g := by cases g; rfl
@[simp] theorem error_roundtrip (e : AspisR1Stage2.verifier.Error) : fromError (error e) = e := by cases e <;> rfl
@[simp] theorem current_error_roundtrip (e : AspisR1CurrentCaller.verifier.Error) : error (fromError e) = e := by cases e <;> rfl

def preparedEquiv : C.P ≃ S.P :=
  ⟨prepared,unPrepared,current_prepared_roundtrip,prepared_roundtrip⟩

#print axioms variant_roundtrip
#print axioms current_variant_roundtrip
#print axioms prepared_roundtrip
#print axioms current_prepared_roundtrip
#print axioms geometry_roundtrip
#print axioms current_geometry_roundtrip
#print axioms error_roundtrip
#print axioms current_error_roundtrip
#print axioms preparedEquiv
end AspisR1.DrvC_Carriers
end
