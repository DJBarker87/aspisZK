import LIB_VArray
import LIB_Env
import NGX_Payload
set_option autoImplicit false
noncomputable section
namespace LIB_VRecords
open Aeneas Aeneas.Std LIB_VCarriers
open AspisR1 AspisR1PublicPreparation
def host {A E : Type} : core.result.Result A E → Except E A
 | .Ok a => .ok a | .Err e => .error e
def raw {A E : Type} : Except E A → core.result.Result A E
 | .ok a => .Ok a | .error e => .Err e
theorem raw_host {A E : Type} (r : core.result.Result A E) : raw (host r) = r := by cases r <;> rfl
def row (n : Nat) : U8 := U8.ofNat (n%256) (by omega)
theorem row_val (r : U8) : row r.val = r := by
 apply UScalar.val_eq_imp
 change r.val%256=r.val
 exact Nat.mod_eq_of_lt (by scalar_tac)
theorem validated_total (p : Prefix) (r : U8) :
 ∃ out, r1_wire.Prefix.validated_record (prefixRaw p) r = .ok out := by
 by_cases live : r.val<27
 · obtain ⟨record,getter,_,_⟩ := NIX_ProducerInstall.framed p.source p.parsed p.parse_eq r live
   exact ⟨.Ok record,getter⟩
 · rw [NFU_PrefixRecords.validated_record]
   have outside : r >= 27#u8 := by change r.val≥27;omega
   simp only [NFU_PrefixRecords.selected,outside,ite_true,NFU_PrefixRecords.token,Result.bind_tc_ok]
   exact ⟨_,rfl⟩
def validatedRecord (p : Prefix) (n : Nat) : Except WErr Record :=
 host (Classical.choose (validated_total p (row n)))
theorem validated_exact (p : Prefix) (r : U8) :
 r1_wire.Prefix.validated_record (prefixRaw p) r = .ok (raw (validatedRecord p r.val)) := by
 unfold validatedRecord
 rw [row_val,raw_host]
 exact Classical.choose_spec (validated_total p r)
theorem selected_of_validated (p : r1_wire.Prefix) (r : U8) (record : Record)
 (h : r1_wire.Prefix.validated_record p r = .ok (.Ok record)) :
 NFU_PrefixRecords.selected p r = .ok (.Ok record.framed) := by
 rw [NFU_PrefixRecords.validated_record] at h
 unfold NFU_PrefixRecords.token at h
 cases q : NFU_PrefixRecords.selected p r with
 | fail e => simp only [q,Result.bind_tc_fail] at h;cases h
 | div => simp only [q,Result.bind_tc_div] at h;cases h
 | ok reply =>
  cases reply with
  | Err e => simp only [q,Result.bind_tc_ok] at h;cases h
  | Ok bytes =>
   simp only [q,Result.bind_tc_ok] at h
   have same := core.result.Result.Ok.inj (Result.ok.inj h)
   exact congrArg (fun x : Record => .ok (.Ok x.framed)) same
 theorem payload_total (p : Prefix) (r : U8) :
 ∃ out, FinishModel.payload (prefixRaw p) r = .ok out := by
 rw [NGX_Payload.source]
 by_cases live : r.val<27
 · obtain ⟨record,getter,_,geometry⟩ := NIX_ProducerInstall.framed p.source p.parsed p.parse_eq r live
   rw [selected_of_validated _ _ _ getter]
   obtain ⟨bytes,run,_,_⟩ := NGX_Payload.tail_total record.framed (by
    rw [geometry]
    exact (NGX_PrefixGeometry.widths r.val).1)
   exact ⟨.Ok bytes,run⟩
 · have outside : r >= 27#u8 := by change r.val≥27;omega
   simp only [NFU_PrefixRecords.selected,outside,ite_true]
   exact ⟨.Err .InvalidRow,rfl⟩
def payload (p : Prefix) (n : Nat) : Except WErr RSL.Bytes :=
 (host (Classical.choose (payload_total p (row n)))).map LIB_Carriers.bytes
theorem payload_exact (p : Prefix) (r : U8) :
 payload p r.val = (host (Classical.choose (payload_total p r))).map LIB_Carriers.bytes := by
 unfold payload
 rw [row_val]
abbrev state := LIB_VCarriers.state
theorem state_exact (D : aspis_core.Digest32 Unit) (t : Transcript) :
 r1_wire.SemanticTranscript.impl.state D t = .ok (LIB_Env.nativeKey (state t)) := by
 rw [NGX_StateImpl.source]
 congr 1
 apply LIB_Carriers.b32_injective
 exact (LIB_Env.key_roundtrip _).symm
#print axioms raw_host
#print axioms row_val
#print axioms validated_total
#print axioms validated_exact
#print axioms selected_of_validated
#print axioms payload_total
#print axioms payload_exact
#print axioms state_exact
end LIB_VRecords
