import LIB_Instances
import Op3I_Header
import LIB_VLibR4
set_option autoImplicit false
namespace AspisR1.NNG_DomainFinding094
open RSL

theorem bind_inherits {A B : Type} (property : Prop) (head : Spec A) (tail : A → Spec B)
 (env : Env) (o : Obs B) (all : ∀ before,head env before → property)
 (law : Spec.bind head tail env o) : property := by
 rcases law with ⟨a,ev,after,called,_,_⟩ | ⟨ev,called,_⟩ | ⟨ev,called,_⟩
 · exact all _ called
 · exact all _ called
 · exact all _ called
#print axioms bind_inherits

/-- The concrete parseShape domain is required even on its rejecting arm.
This is a finding about the installed interface, not a proposed row domain. -/
theorem required_width (a : TX1_094.Args LIB_Instances.VL) (env : Env)
 (o : Obs (Except LIB_Instances.VL.VErr Bytes)) (k : a.k=10)
 (law : TX1_094.Ref LIB_Instances.VL LIB_Instances.P a env o) : a.proof.length=57607 := by
 unfold TX1_094.Ref at law
 have guard : (a.k != SPLIT)=false:=by rw [k];rfl
 rw [guard] at law
 change Spec.bind (Spec.pure (.ok () : Except LIB_VCarriers.VErr Unit)) _ env o at law
 rw [Spec.bind_pure] at law
 exact bind_inherits _ _ _ env o (fun before called=>called.1) law
#print axioms required_width

/-- Conditional only on the row's existing public input domain. At an empty
proof, every total producer contradicts the concrete reference. -/
theorem rejects_all_implementations (pub : LIB_Instances.VL.Public)
 (publicDom : LIB_Instances.VL.publicDom pub)
 (impl : TX1_094.Args LIB_Instances.VL → Observer → Env → Obs (Except LIB_Instances.VL.VErr Bytes)) :
 ¬ TX1_094.RowSpec_094 LIB_Instances.VL LIB_Instances.P impl := by
 intro candidate
 let a : TX1_094.Args LIB_Instances.VL:=⟨pub,[],[],10⟩
 have law:=candidate a none env0 ⟨rfl,publicDom⟩
 have width:=required_width a env0 (impl a none env0) rfl law
 change 0=57607 at width
 cases width
#print axioms rejects_all_implementations
theorem empty_rejected (ops : Op3I_Source.ParseShapeOps) :
 Op3I_Source.verifier.candidate.parse_shape ops
  (⟨[],by simp⟩ : Aeneas.Std.Slice Aeneas.Std.U8)=
  Aeneas.Std.Result.ok (.Err Op3I_Source.verifier.Error.Parse) := by
 simp only [Op3I_Source.verifier.candidate.parse_shape,Op3I_Header.proof_bytes,Aeneas.Std.bind_tc_ok]
 rfl
#print axioms empty_rejected
end AspisR1.NNG_DomainFinding094
