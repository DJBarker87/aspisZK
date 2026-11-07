import PV_THR2_SourceStoreLibrary
set_option autoImplicit false
noncomputable section
namespace PV_THR2_SourceStoreInterpreter
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_SourceStoreNative PV_THR2_SourceStoreLibrary

/-- Concrete, enlarged interpreter with all five library Store meanings
installed. Values supplies native pointer/layout/allocation VALUES only.
There is no Store-transformer parameter or store-write MachineSpec premise.
Invalid reference/layout decoding is visible as undefined, never silently
replaced by an identity delta. Full native replies are delivered unchanged
whenever the source operation is defined, on every answer branch. -/
def step {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (values : Values W E) (s : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.State W E :=
  match s.current.status with
  | .running c => match PV_THR2_Catch316Segment.select c with
    | some _ => PV_THR2_IntrinsicState.step C ctl programs H s
    | none => match select programs c with
      | none => PV_THR2_IntrinsicState.step C ctl programs H s
      | some site =>
        let reply := H site.waiting.request s.current.world
        match interpret C values site.meaning site.callee site.arguments
            c.store s.current.world reply with
        | none => ⟨⟨.undefined none c.store,reply.world,
            s.current.events ++ reply.events⟩,s.suspended⟩
        | some store =>
          let q := PV_THR2_ChildBoundary.delivered C {c with store := store}
            site.waiting reply
          ⟨⟨q.status,q.world,s.current.events ++ q.events⟩,s.suspended⟩
  | _ => PV_THR2_IntrinsicState.step C ctl programs H s

def advance {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (values : Values W E) : Nat → PV_THR2_IntrinsicState.State W E →
      PV_THR2_IntrinsicState.State W E
  | 0,s => s
  | n+1,s => advance C ctl programs H values n (step C ctl programs H values s)

/-- At a selected native site, one step delivers precisely the original full
reply on the source meaning's final Store. No successful-answer hypothesis. -/
theorem native {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (values : Values W E) (c : Config) (w : W) (es : List E)
    (stack : List Config) (site : PV_THR2_SourceStoreNative.Site) (store : Store Data)
    (ordinary : PV_THR2_Catch316Segment.select c = none)
    (selected : select programs c = some site)
    (meaning : interpret C values site.meaning site.callee site.arguments c.store w
      (H site.waiting.request w) = some store) :
    step C ctl programs H values ⟨⟨.running c,w,es⟩,stack⟩ =
      let q := PV_THR2_ChildBoundary.delivered C {c with store := store}
        site.waiting (H site.waiting.request w)
      ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
  simp only [step,ordinary,selected,meaning]

/-- Every post-world, event suffix and suspended frame survives even a
representation gap. The answer rule itself is unchanged on defined meanings. -/
theorem effects {W E : Type} (C : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (values : Values W E) (c : Config) (w : W) (es : List E)
    (stack : List Config) (site : PV_THR2_SourceStoreNative.Site)
    (ordinary : PV_THR2_Catch316Segment.select c = none)
    (selected : select programs c = some site) :
    let r := H site.waiting.request w
    let out := step C ctl programs H values ⟨⟨.running c,w,es⟩,stack⟩
    out.current.world = r.world ∧ out.current.events = es ++ r.events ∧
      out.suspended = stack := by
  dsimp only
  cases meaning : interpret C values site.meaning site.callee site.arguments
      c.store w (H site.waiting.request w) with
  | none => simp [step,ordinary,selected,meaning]
  | some store =>
    rw [native C ctl programs H values c w es stack site store ordinary selected meaning]
    have h := PV_THR2_ChildBoundary.effects C {c with store := store}
      site.waiting (H site.waiting.request w)
    exact ⟨h.1,congrArg (es ++ ·) h.2,rfl⟩

#print axioms step
#print axioms advance
#print axioms native
#print axioms effects
end PV_THR2_SourceStoreInterpreter
