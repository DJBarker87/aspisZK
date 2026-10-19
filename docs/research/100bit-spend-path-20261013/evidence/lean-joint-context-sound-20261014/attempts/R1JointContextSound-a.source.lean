import R1JointContext

/-! Invert the joint context parser and expose its canonical message checks. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.JointContextSound

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

theorem parse_sound (p : Params M Cv L) (pubBytes : Bytes) (tag : Byte)
    (semanticFuel openingFuel : Nat) (c : Addr L) (T : Table (Addr L) State)
    (ctx : JointContext.Context M L)
    (h : JointContext.parse p pubBytes tag semanticFuel openingFuel c T = some ctx) :
    ∃ (previous : State) (ql : Byte) (qd : Bytes) (nl : Byte) (nd : Bytes)
      (xs : List State),
      parseAbsorb c = some (ctx.endpoint, nl, nd) ∧
      DuplexSeek.seek p T 9 ctx.endpoint = some (ctx.queryAddress, xs) ∧
      parseAbsorb ctx.queryAddress = some (previous, ql, qd) ∧
      OpeningPrefixCompletion.typed p pubBytes tag T semanticFuel openingFuel previous =
        some (ctx.c1, ctx.records) ∧
      IndexedMessage.read p ctx.records.length ql qd = some ctx.queryMessage ∧
      IndexedMessage.read p (ctx.records.length + 1) nl nd = some ctx.nextMessage := by
  cases ctx with
  | mk endpoint queryAddress c1 records queryMessage nextMessage =>
    unfold JointContext.parse at h
    cases hc : parseAbsorb c with
    | none => simp [hc] at h
    | some current =>
      rcases current with ⟨endpoint', nl, nd⟩
      cases hs : DuplexSeek.seek p T 9 endpoint' with
      | none => simp [hc, hs] at h
      | some found =>
        rcases found with ⟨a, xs⟩
        cases ha : parseAbsorb a with
        | none => simp [hc, hs, ha] at h
        | some query =>
          rcases query with ⟨previous, ql, qd⟩
          cases ht : OpeningPrefixCompletion.typed p pubBytes tag T
              semanticFuel openingFuel previous with
          | none => simp [hc, hs, ha, ht] at h
          | some decoded =>
            rcases decoded with ⟨c1', records'⟩
            cases hq : IndexedMessage.read p records'.length ql qd with
            | none => simp [hc, hs, ha, ht, hq] at h
            | some qm =>
              cases hn : IndexedMessage.read p (records'.length + 1) nl nd with
              | none => simp [hc, hs, ha, ht, hq, hn] at h
              | some nm =>
                have hctx :
                    (⟨endpoint', a, c1', records', qm, nm⟩ : JointContext.Context M L) =
                      ⟨endpoint, queryAddress, c1, records, queryMessage, nextMessage⟩ := by
                  simpa [hc, hs, ha, ht, hq, hn] using h
                cases hctx
                exact ⟨previous, ql, qd, nl, nd, xs, hc, hs, ha, ht, hq, hn⟩

theorem canonical_messages (p : Params M Cv L) (pubBytes : Bytes) (tag : Byte)
    (semanticFuel openingFuel : Nat) (c : Addr L) (T : Table (Addr L) State)
    (ctx : JointContext.Context M L)
    (h : JointContext.parse p pubBytes tag semanticFuel openingFuel c T = some ctx) :
    ∃ (previous : State) (ql : Byte) (qd : Bytes) (nl : Byte) (nd : Bytes)
      (xs : List State),
      parseAbsorb c = some (ctx.endpoint, nl, nd) ∧
      DuplexSeek.seek p T 9 ctx.endpoint = some (ctx.queryAddress, xs) ∧
      parseAbsorb ctx.queryAddress = some (previous, ql, qd) ∧
      OpeningPrefixCompletion.typed p pubBytes tag T semanticFuel openingFuel previous =
        some (ctx.c1, ctx.records) ∧
      ql = p.lbl ctx.records.length ∧
      p.dec qd = some ctx.queryMessage ∧
      p.enc ctx.queryMessage = qd ∧
      nl = p.lbl (ctx.records.length + 1) ∧
      p.dec nd = some ctx.nextMessage ∧
      p.enc ctx.nextMessage = nd := by
  obtain ⟨previous, ql, qd, nl, nd, xs, hc, hs, ha, ht, hq, hn⟩ :=
    parse_sound p pubBytes tag semanticFuel openingFuel c T ctx h
  obtain ⟨hql, hdq, heq⟩ := IndexedMessage.read_sound p ctx.records.length
    ql qd ctx.queryMessage hq
  obtain ⟨hnl, hdn, hen⟩ := IndexedMessage.read_sound p (ctx.records.length + 1)
    nl nd ctx.nextMessage hn
  exact ⟨previous, ql, qd, nl, nd, xs, hc, hs, ha, ht,
    hql, hdq, heq, hnl, hdn, hen⟩

#print axioms parse_sound
#print axioms canonical_messages
end AspisR1.JointContextSound
end
