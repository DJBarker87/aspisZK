namespace PV_O11_KindView
/-- A source-view transport, not a second extraction of std::io::Error.
The payloads retain ownership identity; kind only borrows them. -/
inductive View (K C M : Type) where
  | os : Int → View K C M
  | custom : C → View K C M
  | simple : K → View K C M
  | message : M → View K C M

def project {K C M : Type} (osKind : Int → K)
    (customKind : C → K) (messageKind : M → K) : View K C M → K
  | .os n => osKind n
  | .custom c => customKind c
  | .simple k => k
  | .message m => messageKind m

/-- Four-arm source control flow from the complete deployed getter body.
No native Error representation or errno decoder is assumed to be this view. -/
def source {E K C M : Type} (data : E → View K C M)
    (osKind : Int → K) (customKind : C → K) (messageKind : M → K)
    (e : E) : Except Unit K :=
  match data e with
  | .os n => .ok (osKind n)
  | .custom c => .ok (customKind c)
  | .simple k => .ok k
  | .message m => .ok (messageKind m)

theorem complete {E K C M : Type} (data : E → View K C M)
    (osKind : Int → K) (customKind : C → K) (messageKind : M → K) (e : E) :
    source data osKind customKind messageKind e =
      .ok (project osKind customKind messageKind (data e)) := by
  cases h : data e <;> simp only [source, h, project]

/-- The getter model returns the same world, borrowed error and payloads.
This does not prove the native data/load interpretation. -/
def run {E K C M W : Type} (data : E → View K C M)
    (osKind : Int → K) (customKind : C → K) (messageKind : M → K)
    (e : E) (w : W) : Except Unit (K × E × W) := do
  let k ← source data osKind customKind messageKind e
  .ok (k,e,w)

theorem frame {E K C M W : Type} (data : E → View K C M)
    (osKind : Int → K) (customKind : C → K) (messageKind : M → K)
    (e : E) (w : W) :
    run data osKind customKind messageKind e w =
      .ok (project osKind customKind messageKind (data e),e,w) := by
  unfold run
  rw [complete]
  rfl

/-- Exact condition left to discharge to transfer an existing getter law.
All quantifiers are retained, including every dynamic payload. -/
theorem transport {E K C M : Type} (data : E → View K C M)
    (osKind : Int → K) (customKind : C → K) (messageKind : M → K)
    (native : E → Except Unit K)
    (binding : ∀ e, native e = source data osKind customKind messageKind e) :
    ∀ e, native e = .ok (project osKind customKind messageKind (data e)) := by
  intro e
  rw [binding,complete]

#print axioms complete
#print axioms frame
#print axioms transport
end PV_O11_KindView
