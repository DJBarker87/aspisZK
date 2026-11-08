import NNG_ProjectionBind345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DecodeProjection345
open RSL NNG_Phases345 NNG_Obs345 NNG_Pure345
open NNG_LogicalProjection345 (V C)

theorem transport (s : PublicData) (next : Decoded V C → Obs (Except ProgramError Bytes))
 (r r' : Option C.Statement) (eq : r=r') (h : C.decodeStatement s.publicData=r) :
 afterDecode V C (fun _=>true) s next r h=
 afterDecode V C (fun _=>true) s next r' (h.trans eq) := by
 cases eq
 rfl
#print axioms transport

theorem source (s : PublicData) (next : Decoded V C → Obs (Except ProgramError Bytes))
 (later : ∀ d,next (NNG_LogicalProjection345.decoded d)=next d) :
 stepDecode V C (fun _=>true) (NNG_LogicalProjection345.publicData s) next=
 stepDecode V C (fun _=>true) s next := by
 have go (r : Option C.Statement) (h : C.decodeStatement s.publicData=r) :
  afterDecode V C (fun _=>true) (NNG_LogicalProjection345.publicData s) next r
   ((NNG_Cut345.decode s.publicData).trans h)=
  afterDecode V C (fun _=>true) s next r h := by
  cases r with
  | none=>rfl
  | some st=>exact later ⟨s,st,h⟩
 unfold stepDecode
 rw [NNG_ProjectionBind345.allocation,NNG_ProjectionBind345.allocation]
 exact (transport (NNG_LogicalProjection345.publicData s) next _ _
  (NNG_Cut345.decode s.publicData) rfl).trans (go _ rfl)
#print axioms source
end AspisR1.NNG_DecodeProjection345
