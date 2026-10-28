"""Exact native carriers; retain every error variant and unselected dictionary field."""
from pathlib import Path
import sys
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
errors=['Parse','Semantic','Transcript','Relation','Merkle','Query','Checkpoint','Allocation','Rejected','AttemptsExhausted','Entropy']
s='''import R1Z.PV_B2_F_AllocationTransport
import R1Z.PV_B2_E_GammaOriginal
set_option autoImplicit false
noncomputable section
namespace PV_B2_F_MaterializeNative
open Aeneas Aeneas.Std Result
open PV_B2_C_MutationStep
abbrev Native := ProverRwFull.aspis_core.field.wide_exact.WideExact
abbrev W := PV_B2_251c1.host_weights.Weights
abbrev Outcome := PV_B2_F_AllocationTransport.Outcome

def toNative (v : E) : Native :=
  ⟨⟨⟨v.c0.c0.a,v.c0.c0.b⟩,⟨v.c0.c1.a,v.c0.c1.b⟩⟩,
   ⟨⟨v.c1.c0.a,v.c1.c0.b⟩,⟨v.c1.c1.a,v.c1.c1.b⟩⟩⟩
def fromNative (v : Native) : E :=
  ⟨⟨⟨v.c0.c0.a,v.c0.c0.b⟩,⟨v.c0.c1.a,v.c0.c1.b⟩⟩,
   ⟨⟨v.c1.c0.a,v.c1.c0.b⟩,⟨v.c1.c1.a,v.c1.c1.b⟩⟩⟩
theorem roundtrip (v : E) : fromNative (toNative v)=v := by cases v; rfl
theorem roundtrip_native (v : Native) : toNative (fromNative v)=v := by cases v; rfl

def toVec (out : Out) : alloc.vec.Vec Native :=
  ⟨out.val.map toNative,by rw [List.length_map,out.property]; scalar_tac⟩
def toError : PV_B2_251c1.verifier.Error → ProverRwFull.verifier.Error
'''+''.join(f'  | .{e} => .{e}\n' for e in errors)+'''def mapRust : PV_B2_F_AllocationTransport.RustResult →
    core.result.Result (alloc.vec.Vec Native) ProverRwFull.verifier.Error
  | .Ok out => .Ok (toVec out)
  | .Err e => .Err (toError e)

def types (base : ProverRwFull.ExternalTypes) : ProverRwFull.ExternalTypes :=
  {base with op25 := W}

def callback (event : Outcome) (w : W) (kappa : Native) :
    Result (core.result.Result (alloc.vec.Vec Native) ProverRwFull.verifier.Error) :=
  PV_B2_E_OrdinaryOriginal.mapResult mapRust
    (PV_B2_F_AllocationTransport.copied event w (fromNative kappa))
def originalCallback (event : Outcome) (w : W) (kappa : Native) :
    Result (core.result.Result (alloc.vec.Vec Native) ProverRwFull.verifier.Error) :=
  PV_B2_E_OrdinaryOriginal.mapResult mapRust
    (PV_B2_F_AllocationTransport.original event w (fromNative kappa))

def selected (base : ProverRwFull.ExternalTypes) (event : Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) : @ProverRwFull.ExternalFuns (types base) :=
  {PV_B2_E_GammaOriginal.selected ops with op251 := callback event}
def originalDictionary (base : ProverRwFull.ExternalTypes) (event : Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) : @ProverRwFull.ExternalFuns (types base) :=
  {PV_B2_E_GammaOriginal.originalDictionary ops with op251 := originalCallback event}

theorem callbacks (event : Outcome) (w : W) (kappa : Native) :
    callback event w kappa = originalCallback event w kappa := by
  unfold callback originalCallback
  rw [PV_B2_F_AllocationTransport.equal]

theorem selected_callback (base : ProverRwFull.ExternalTypes) (event : Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (kappa : Native) :
    (selected base event ops).op251 w kappa = originalCallback event w kappa :=
  callbacks event w kappa

theorem nonvacuity (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (kappa : Native) :
    ∃ out, (selected base .supplied ops).op251 w kappa = ok (.Ok out) := by
  obtain ⟨out,ho⟩ := PV_B2_F_AllocationTransport.supplied w (fromNative kappa)
  exact ⟨toVec out,by change PV_B2_E_OrdinaryOriginal.mapResult mapRust _ = _; rw [ho]; rfl⟩

theorem allocation_error (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (kappa : Native) :
    (selected base .denied ops).op251 w kappa = ok (.Err ProverRwFull.verifier.Error.Allocation) := rfl

theorem dictionaries (base : ProverRwFull.ExternalTypes) (event : Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    selected base event ops = originalDictionary base event ops := by
  have hc : callback event = originalCallback event := by
    funext w kappa
    exact callbacks event w kappa
  unfold selected originalDictionary
  rw [PV_B2_E_GammaOriginal.dictionaries,hc]

theorem observations {O : Sort _} (observe : @ProverRwFull.ExternalFuns (types base) → O)
    (base : ProverRwFull.ExternalTypes) (event : Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    observe (selected base event ops)=observe (originalDictionary base event ops) :=
  congrArg observe (dictionaries base event ops)
'''
# Keep the base binder before it is referenced under autoImplicit=false.
s=s.replace('theorem observations {O : Sort _} (observe : @ProverRwFull.ExternalFuns (types base) → O)\n    (base : ProverRwFull.ExternalTypes)', 'theorem observations {O : Sort _} (base : ProverRwFull.ExternalTypes)\n    (observe : @ProverRwFull.ExternalFuns (types base) → O)')
for n in range(262):
 if n in [249,250,251]:continue
 s+=f'''theorem preserved_{n} (base : ProverRwFull.ExternalTypes) (event : Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op{n} _ (selected base event ops) =
      @ProverRwFull.ExternalFuns.op{n} _ ops := PV_B2_E_GammaOriginal.preserved_{n} ops
'''
for name in ['roundtrip','roundtrip_native','callbacks','selected_callback','nonvacuity','allocation_error','dictionaries','observations']+[f'preserved_{n}' for n in range(262) if n not in [249,250,251]]:s+='#print axioms '+name+'\n'
s+='end PV_B2_F_MaterializeNative\n'
p=L/'PV_B2_F_MaterializeNative.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
