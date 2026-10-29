import R1Z.ProverRwRngOwnerCertificate
import Mathlib.Data.Fintype.Pi

/-! A finite carrier for the D193 prototype, including error replies.
This is not a probability law for OS errors and not a deployed FS instance.
The single cursor is retained across calls; it is never reset per attempt. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_World
open Aeneas Aeneas.Std Result ControlFlow ProverRwRng
open ProverRwRngOwnerStep ProverRwRngOwnerEvents ProverRwRngOwnerInventory

abbrev Byte := Fin 256
abbrev RawReply := (Fin 64 → Byte) × Option Byte
abbrev RawTape := Fin 128 → RawReply

def byte (b : Byte) : U8 := UScalar.ofNatCore b.val b.isLt

def reply (r : RawReply) : ProverRwRngTape.Reply :=
  (⟨List.ofFn (fun i => byte (r.1 i)), by simp⟩,
    match r.2 with
    | none => .Ok ()
    | some error => .Err (byte error))

def replies (raw : RawTape) : List ProverRwRngTape.Reply :=
  List.ofFn (fun i => reply (raw i))

theorem replies_length (raw : RawTape) : (replies raw).length = 128 := by
  simp only [replies,List.length_ofFn]

def provider (raw : RawTape) (used : Usize) : Tape :=
  ProverRwRngTape.tape (replies raw)
    (by rw [replies_length]; scalar_tac) used

instance raw_finite : Fintype RawTape := inferInstance
instance raw_nonempty : Nonempty RawTape := inferInstance

theorem reply_at (raw : RawTape) (i : Fin 128) :
    (provider raw 0#usize).replies.val[i.val]? = some (reply (raw i)) := by
  simp only [provider,ProverRwRngTape.tape,replies,List.getElem?_ofFn,dif_pos i.isLt]

variable [ErasureFns]

/-- D193, specialized to the explicit finite carrier. All replies, including
errors and rejected zero blocks, retain their actual positions. The .ok guard
is extraction execution, not successful native entropy or proof generation. -/
theorem finite_owner (raw : RawTape) (used : Usize)
    (nonce : Array U8 32#usize) :
    ProverRwRng.old_owner nonce (provider raw used) =
      ProverRwRng.owner nonce (provider raw used) ∧
    ∀ after status,
      ProverRwRng.owner nonce (provider raw used) = .ok (after,status) →
      ∃ states,
        OwnerReplay (oldBody nonce) Prod.swap nonce (provider raw used) states (after,status) ∧
        OwnerReplay (newBody nonce) id nonce (provider raw used) states (after,status) ∧
        after.replies = (provider raw used).replies ∧
        after.used.val = used.val + drawCount states ∧
        drawCount states ≤ 16 ∧
        events states = (List.range' used.val (drawCount states)).map
          (fun index => (Array.repeat 64#usize 0#u8,index,(replies raw)[index]?)) ∧
        (∀ event ∈ events states, event.2.2.isSome = true) ∧
        after.replies.val.drop after.used.val =
          (replies raw).drop (used.val + drawCount states) := by
  exact ProverRwRngOwnerCertificate.universal_cap16 nonce (provider raw used)

/-- Sequential admitted owner executions share one provider. This relation
includes entropy error statuses; it assumes no equality of outputs or traces.
It does not install the native cap8 callback or choose its nonce policy. -/
inductive Owners : Tape → List (List State) → Tape → Prop
  | nil (p : Tape) : Owners p [] p
  | cons {p next final : Tape} {states : List State} {rest : List (List State)}
      (nonce : Array U8 32#usize) (status : ProverRwRngControl.Status)
      (run : ProverRwRng.owner nonce p = .ok (next,status))
      (trace : OwnerReplay (newBody nonce) id nonce p states (next,status))
      (tail : Owners next rest final) : Owners p (states :: rest) final

def count (calls : List (List State)) : Nat :=
  (calls.map drawCount).sum

def log (calls : List (List State)) : List Event := calls.flatMap events

theorem owner_inventory {nonce : Array U8 32#usize} {p next : Tape}
    {status : ProverRwRngControl.Status} {states : List State}
    (trace : OwnerReplay (newBody nonce) id nonce p states (next,status)) :
    next.replies = p.replies ∧ next.used.val = p.used.val + drawCount states ∧
      drawCount states ≤ 16 ∧
      events states = (List.range' p.used.val (drawCount states)).map
        (fun index => (Array.repeat 64#usize 0#u8,index,p.replies.val[index]?)) := by
  rcases trace with rejected | entered
  · rcases rejected with ⟨_,empty,final⟩
    cases final
    subst states
    exact ⟨rfl,rfl,by decide,rfl⟩
  · rcases entered with ⟨_,raw,replay,final⟩
    change raw = (next,status) at final
    subst raw
    obtain ⟨same,cursor,bound⟩ := replay_inventory nonce replay
    exact ⟨same,cursor,bound.trans (Nat.sub_le 16 _),replay_events nonce replay⟩

theorem owners_inventory {p final : Tape} {calls : List (List State)}
    (runs : Owners p calls final) :
    final.replies = p.replies ∧ final.used.val = p.used.val + count calls ∧
      count calls ≤ 16 * calls.length ∧
      log calls = (List.range' p.used.val (count calls)).map
        (fun index => (Array.repeat 64#usize 0#u8,index,p.replies.val[index]?)) := by
  induction runs with
  | nil p => exact ⟨rfl,rfl,by simp [count],rfl⟩
  | @cons p next final states rest nonce status run trace tail ih =>
    obtain ⟨same,cursor,bound,ordered⟩ := owner_inventory trace
    rcases ih with ⟨sameTail,cursorTail,boundTail,orderedTail⟩
    have counts : count (states :: rest) = drawCount states + count rest := by
      simp only [count,List.map_cons,List.sum_cons]
    refine ⟨sameTail.trans same,?_,?_,?_⟩
    · rw [counts,cursorTail,cursor,Nat.add_assoc]
    · rw [counts,List.length_cons]
      omega
    · change events states ++ log rest = _
      rw [ordered,orderedTail,same,cursor,counts,← List.map_append,← List.range'_append]
      simp only [Nat.one_mul]

/-- Eight source-owner calls cannot consume beyond the common 128-reply
budget from cursor zero. This is a capacity/ordered-event fact, not an entropy
uniformity or native callback theorem. -/
theorem cap8_inventory (raw : RawTape) {final : Tape} {calls : List (List State)}
    (runs : Owners (provider raw 0#usize) calls final) (cap : calls.length ≤ 8) :
    final.replies.val = replies raw ∧ final.used.val = count calls ∧
      count calls ≤ 128 ∧
      log calls = (List.range' 0 (count calls)).map
        (fun index => (Array.repeat 64#usize 0#u8,index,(replies raw)[index]?)) ∧
      final.replies.val.drop final.used.val = (replies raw).drop (count calls) := by
  obtain ⟨same,cursor,bounded,ordered⟩ := owners_inventory runs
  change final.used.val = 0 + count calls at cursor
  have cursor' : final.used.val = count calls := by simpa only [Nat.zero_add] using cursor
  have same' : final.replies.val = replies raw := congrArg (fun v => v.val) same
  refine ⟨same',cursor',by omega,ordered,?_⟩
  rw [same',cursor']

#print axioms byte
#print axioms reply
#print axioms replies_length
#print axioms provider
#print axioms raw_finite
#print axioms raw_nonempty
#print axioms reply_at
#print axioms finite_owner
#print axioms owner_inventory
#print axioms owners_inventory
#print axioms cap8_inventory
end R1Z.PV_RunJoin_World
