import R1PublicSourceRawMap

/-! PROPOSED, not yet compiled. A successful execution of the raw-u32
serializer supplies all canonical-limb guards. These are facts about the
handwritten Lean model only; no Rust extraction/refinement is asserted. -/
set_option autoImplicit false
namespace AspisR1.PublicSourceRawSuccess

open PublicSourceRaw

theorem fields_success (xs : List Word) (bytes : Bytes)
    (h : fields xs = some bytes) : ∀ x ∈ xs, fieldCanonical x := by
  induction xs generalizing bytes with
  | nil => simp
  | cons x xs ih =>
      by_cases hc : fieldCanonical x
      · have ht : ∃ tail, fields xs = some tail := by
          cases htail : fields xs with
          | none => simp [fields, hc, htail] at h
          | some tail => exact ⟨tail, by simp only [htail]⟩
        obtain ⟨tail, htail⟩ := ht
        intro y hy
        rcases List.mem_cons.mp hy with hxy | hy
        · simpa only [hxy] using hc
        · exact ih tail htail y hy
      · simp [fields, hc] at h

theorem digestBytes_success (d : Digest) (bytes : Bytes)
    (h : digestBytes d = some bytes) : ∀ i, fieldCanonical (d i) := by
  intro i
  exact fields_success (List.ofFn d) bytes h (d i)
    (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem digests_success (ds : List Digest) (bytes : Bytes)
    (h : digests ds = some bytes) :
    ∀ d ∈ ds, ∀ i, fieldCanonical (d i) := by
  induction ds generalizing bytes with
  | nil => simp
  | cons d ds ih =>
      cases hd : digestBytes d with
      | none => simp [digests, hd] at h
      | some head =>
          cases ht : digests ds with
          | none => simp [digests, hd, ht] at h
          | some tail =>
              intro e he i
              rcases List.mem_cons.mp he with hed | he
              · subst e
                exact digestBytes_success d head hd i
              · exact ih tail ht e he i

theorem frontierBytes_success (f : Frontier) (bytes : Bytes)
    (h : frontierBytes f = some bytes) :
    ∀ l i, fieldCanonical (f l i) := by
  intro l i
  exact digests_success (List.ofFn f) bytes h (f l)
    (List.mem_ofFn.mpr ⟨l, rfl⟩) i

theorem header_success (c : Common) (bytes : Bytes)
    (h : header c = some bytes) :
    (∀ i, fieldCanonical (c.anchor i)) ∧
    (∀ i, fieldCanonical (c.nullifier i)) ∧ fieldCanonical c.assetId := by
  cases ha : digestBytes c.anchor with
  | none => simp [header, ha] at h
  | some anchor =>
      cases hn : digestBytes c.nullifier with
      | none => simp [header, ha, hn] at h
      | some nullifier =>
          cases hx : fields [c.assetId] with
          | none => simp [header, ha, hn, hx] at h
          | some asset =>
              exact ⟨digestBytes_success c.anchor anchor ha,
                digestBytes_success c.nullifier nullifier hn,
                fields_success [c.assetId] asset hx c.assetId (by simp)⟩

theorem afterBytes_success (c : Common) (bytes : Bytes)
    (h : afterBytes c = some bytes) :
    (∀ l i, fieldCanonical (c.snapshotFrontier l i)) ∧
    (∀ i, fieldCanonical (c.nextRoot i)) ∧
    (∀ l i, fieldCanonical (c.nextFrontier l i)) := by
  cases hs : frontierBytes c.snapshotFrontier with
  | none => simp [afterBytes, hs] at h
  | some snapshot =>
      cases hr : digestBytes c.nextRoot with
      | none => simp [afterBytes, hs, hr] at h
      | some root =>
          cases hn : frontierBytes c.nextFrontier with
          | none => simp [afterBytes, hs, hr, hn] at h
          | some next =>
              exact ⟨frontierBytes_success c.snapshotFrontier snapshot hs,
                digestBytes_success c.nextRoot root hr,
                frontierBytes_success c.nextFrontier next hn⟩

theorem serialize_success_canonical (p : Public) (bytes : Bytes)
    (h : serialize p = some bytes) : Canonical p := by
  cases p with
  | transfer c recipient =>
      cases hh : header c with
      | none => simp [serialize, hh] at h
      | some hd =>
          cases hr : digestBytes recipient with
          | none => simp [serialize, hh, hr] at h
          | some recipientBytes =>
              cases hc : digestBytes c.change with
              | none => simp [serialize, hh, hr, hc] at h
              | some change =>
                  cases ha : afterBytes c with
                  | none => simp [serialize, hh, hr, hc, ha] at h
                  | some after =>
                      obtain ⟨hanchor, hnullifier, hasset⟩ := header_success c hd hh
                      obtain ⟨hsnapshot, hroot, hnext⟩ := afterBytes_success c after ha
                      exact ⟨⟨hanchor, hnullifier, hasset,
                        digestBytes_success c.change change hc,
                        hsnapshot, hroot, hnext⟩,
                        digestBytes_success recipient recipientBytes hr⟩
  | withdrawal c amount =>
      cases hh : header c with
      | none => simp [serialize, hh] at h
      | some hd =>
          cases hc : digestBytes c.change with
          | none => simp [serialize, hh, hc] at h
          | some change =>
              cases hm : fields [amount] with
              | none => simp [serialize, hh, hc, hm] at h
              | some amountBytes =>
                  cases ha : afterBytes c with
                  | none => simp [serialize, hh, hc, hm, ha] at h
                  | some after =>
                      obtain ⟨hanchor, hnullifier, hasset⟩ := header_success c hd hh
                      obtain ⟨hsnapshot, hroot, hnext⟩ := afterBytes_success c after ha
                      exact ⟨⟨hanchor, hnullifier, hasset,
                        digestBytes_success c.change change hc,
                        hsnapshot, hroot, hnext⟩,
                        fields_success [amount] amountBytes hm amount (by simp)⟩

theorem toWire_of_serialize (p : Public) (bytes : Bytes)
    (h : serialize p = some bytes) :
    ∃ wire, toWire p = some wire ∧
      PublicByteCodec.encode (SemanticPublicWire.toPublic wire) = some bytes := by
  have hc := serialize_success_canonical p bytes h
  have hm : toWire p = some (mapPublic p hc) := by simp [toWire, hc]
  refine ⟨mapPublic p hc, hm, ?_⟩
  exact PublicSourceRawMap.encode_of_serialize p _ bytes h ⟨_, hm, rfl⟩

theorem decode_of_serialize (p : Public) (bytes : Bytes)
    (h : serialize p = some bytes) (hn : NonzeroWithdrawal p) :
    ∃ wire, toWire p = some wire ∧
      PublicByteCodec.decode bytes = some (SemanticPublicWire.toPublic wire) := by
  obtain ⟨wire, hw, _⟩ := toWire_of_serialize p bytes h
  exact ⟨wire, hw, PublicSourceRawMap.decode_of_serialize p _ bytes h
    ⟨wire, hw, rfl⟩ hn⟩

#print axioms serialize_success_canonical
#print axioms toWire_of_serialize
#print axioms decode_of_serialize

end AspisR1.PublicSourceRawSuccess
