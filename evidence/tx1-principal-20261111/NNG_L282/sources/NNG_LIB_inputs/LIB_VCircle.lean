import LIB_VCode
set_option autoImplicit false
noncomputable section
namespace LIB_VCircle
open Aeneas Aeneas.Std LIB_VCarriers
open AspisR1 AspisR1PublicPreparation
def project (r : core.result.Result Point WErr × Transcript) : Except WErr (Point × Transcript) :=
 match r.1 with | .Ok p=>.ok (p,r.2) | .Err e=>.error e
def code (a : Transcript × Record) (env : RSL.Env) :=
 NJM_CircleCode.source (LIB_VCode.digest env) a.1 a.2
def circle : RSL.Child (Transcript × Record) (Except WErr (Point × Transcript)) :=
 ⟨fun a=>a.2.framed.val.length≤3717,fun a=>LIB_VCode.law project (code a)⟩
def eval (a : Transcript × Record) (env : RSL.Env) : Except WErr (Point × Transcript) :=
 LIB_VResult.value project (.error .InvalidRow) (PreparedHashCode.run (code a env)).2
theorem law_exact (a : Transcript × Record) (env : RSL.Env) (o : RSL.Obs (Except WErr (Point × Transcript))) :
 circle.law a env o ↔ o=LIB_VCode.obs env project
 (PreparedHashCode.run (NJM_CircleCode.source (LIB_VCode.digest env) a.1 a.2)) := Iff.rfl
theorem caller {Pointer : Type} (env : RSL.Env) (template : NIX_DispatchCut.Pre Pointer)
 (p : Prefix) (t : Transcript) (slot : Fin 27) :
 ∃ record,r1_wire.Prefix.validated_record (prefixRaw p) (NJM_InvocationRoots.row slot)=.ok (.Ok record) ∧
 record.row=NJM_InvocationRoots.row slot ∧
 NJM_InvocationRoots.Circle (LIB_VCode.digest env) template t record := by
 have root := NJM_InvocationRoots.circle (LIB_VCode.digest env) template p.source t slot
 split at root
 · rename_i pre hp
   have same := core.result.Result.Ok.inj (Result.ok.inj (hp.symm.trans p.parse_eq))
   subst pre
   exact root
 · rename_i e hp
   have bad := hp.symm.trans p.parse_eq
   cases bad
 · rename_i e hp
   have bad := hp.symm.trans p.parse_eq
   cases bad
 · rename_i hp
   have bad := hp.symm.trans p.parse_eq
   cases bad
theorem returns (a : Transcript × Record) (env : RSL.Env) :
 NND_Returned.Returns (circle.law a) env (eval a env) :=
 LIB_VResult.returns project (Except.error .InvalidRow : Except WErr (Point × Transcript))
 (fun e=>(PreparedHashCode.run (code a e)).2)
 (fun e=>LIB_VCode.events e (PreparedHashCode.run (code a e)).1) env
theorem functional : RSL.Child.Functional circle := fun _ _ => LIB_VCode.functional _ _
#print axioms law_exact
#print axioms caller
#print axioms returns
#print axioms functional
end LIB_VCircle
