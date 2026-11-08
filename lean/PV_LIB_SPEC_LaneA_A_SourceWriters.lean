import PV_LIB_Observation
import PV_THR2_SourceStoreInterpreter
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_SourceWriters
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_SourceStoreNative PV_THR2_SourceStoreLibrary
/-- The graph consumes the actually selected request and issued store. Its
none branch is the provider interpreter's undefined branch, not identity.
Values is W4's value-only environment; no Store transformer is accepted. -/
def internalModel {W E : Type} (C : Carrier W Data) (values : Values W E)
    (c : Config) (w : W) (es : List E) (stack : List Config)
    (site : PV_THR2_SourceStoreNative.Site) (r : Reply W E Data) : PV_THR2_IntrinsicState.State W E :=
  match interpret C values site.meaning site.callee site.arguments c.store w r with
  | none => ⟨⟨.undefined none c.store,r.world,es ++ r.events⟩,stack⟩
  | some store =>
    let q := PV_THR2_ChildBoundary.delivered C {c with store := store} site.waiting r
    ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩
def model {W E : Type} (C : Carrier W Data) (values : Values W E)
    (c : Config) (w : W) (es : List E) (stack : List Config)
    (site : PV_THR2_SourceStoreNative.Site) (r : Reply W E Data) :=
  PV_LIB.observe (internalModel C values c w es stack site r)
def law {W E : Type} (C : Carrier W Data) (values : Values W E)
    (c : Config) (w : W) (es : List E) (stack : List Config)
    (site : PV_THR2_SourceStoreNative.Site) (r : Reply W E Data) (out : PV_LIB.MachineObservation W E) : Prop :=
  out = model C values c w es stack site r
/-- Every reply is retained. No write-definedness, success, counter equality
or endpoint premise is used. Selection is an internal dispatch condition;
this lemma does not assert that a caller reaches this configuration. -/
theorem installed {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (values : Values W E) (c : Config) (w : W) (es : List E)
    (stack : List Config) (site : PV_THR2_SourceStoreNative.Site)
    (ordinary : PV_THR2_Catch316Segment.select c = none)
    (selected : select programs c = some site) :
    law C values c w es stack site (H site.waiting.request w)
      (PV_LIB.observe (PV_THR2_SourceStoreInterpreter.step C ctl programs H values
        ⟨⟨.running c,w,es⟩,stack⟩)) := by
  unfold law model internalModel PV_THR2_SourceStoreInterpreter.step
  simp only [ordinary,selected]
  rfl
/-- W4's exact named meanings are the four writer graph projections. -/
theorem meanings {W E : Type} (C : Carrier W Data) (values : Values W E)
    (fn : Data) (args : List Data) (s : Store Data) (w : W) (r : Reply W E Data) :
    interpret C values .intoIterNext9 fn args s w r =
      PV_THR2_LibrarySemantics_IntoIterNext9 C values fn args s w ∧
    interpret C values .vecAppend10 fn args s w r =
      PV_THR2_LibrarySemantics_VecAppend10 C values fn args s w r ∧
    interpret C values .rangeNext93 fn args s w r =
      PV_THR2_LibrarySemantics_RangeNext93 C args s w ∧
    interpret C values .vecPush167 fn args s w r =
      PV_THR2_LibrarySemantics_VecPush167 C values fn args s w r :=
  ⟨rfl,rfl,rfl,rfl⟩
#print axioms installed
#print axioms meanings
end PV_LIB_A_SourceWriters
