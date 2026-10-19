import R1SemanticPublicWire

/-! A successful mathematical wire decode reconstructs the exact input list.
The theorem is about the Lean codec only; source-parser correspondence is a
separate obligation. -/
set_option autoImplicit false
namespace AspisR1.SemanticPublicWireSound

open AspisR1.SemanticPublicWire

private theorem expect_sound (tag : Byte) (bytes rest : List Byte)
    (h : expect tag bytes = some rest) : bytes = tag :: rest := by
  cases bytes with
  | nil => simp [expect] at h
  | cons head tail =>
      by_cases hh : head = tag
      · simp [expect, hh] at h
        subst head
        subst rest
        rfl
      · simp [expect, hh] at h

theorem decodeAfter_sound (anchor nullifier : Digest) (assetId : M31)
    (change : Digest) (bytes : List Byte) (c : Common)
    (h : decodeAfter anchor nullifier assetId change bytes = some c) :
    c.anchor = anchor ∧ c.nullifier = nullifier ∧ c.assetId = assetId ∧
      c.change = change ∧ bytes = afterBytes c := by
  unfold decodeAfter at h
  cases hi : readIndex bytes with
  | none => simp [hi] at h
  | some ip =>
      rcases ip with ⟨index, rest1⟩
      simp [hi] at h
      cases hs : readFrontier rest1 with
      | none => simp [hs] at h
      | some sp =>
          rcases sp with ⟨snapshot, rest2⟩
          simp [hs] at h
          cases hr : readDigest rest2 with
          | none => simp [hr] at h
          | some rp =>
              rcases rp with ⟨root, rest3⟩
              simp [hr] at h
              cases hf : readFrontier rest3 with
              | none => simp [hf] at h
              | some fp =>
                  rcases fp with ⟨frontier, rest4⟩
                  simp [hf] at h
                  cases rest4 with
                  | nil =>
                      simp at h
                      have hc : c = ⟨anchor, nullifier, assetId, change,
                          index, snapshot, root, frontier⟩ := h.symm
                      have hiBytes : bytes = PublicIndexListCodec.encode index ++ rest1 :=
                        PublicByteCursor.read_sound 8 PublicIndexListCodec.decode
                          PublicIndexListCodec.encode bytes index rest1
                          (by intro bs x hx; exact PublicIndexListCodec.encode_of_decode bs x hx)
                          hi
                      have hsBytes : rest1 = PublicFieldBlockCodec.encodeFrontier snapshot ++ rest2 :=
                        PublicByteCursor.read_sound 640 PublicFieldBlockCodec.decodeFrontier
                          PublicFieldBlockCodec.encodeFrontier rest1 snapshot rest2
                          (by intro bs x hx; exact PublicFieldBlockCodec.encodeFrontier_of_decodeFrontier bs x hx)
                          hs
                      have hrBytes : rest2 = PublicFieldBlockCodec.encodeDigest root ++ rest3 :=
                        PublicByteCursor.read_sound 32 PublicFieldBlockCodec.decodeDigest
                          PublicFieldBlockCodec.encodeDigest rest2 root rest3
                          (by intro bs x hx; exact PublicFieldBlockCodec.encodeDigest_of_decodeDigest bs x hx)
                          hr
                      have hfBytes : rest3 = PublicFieldBlockCodec.encodeFrontier frontier ++ [] :=
                        PublicByteCursor.read_sound 640 PublicFieldBlockCodec.decodeFrontier
                          PublicFieldBlockCodec.encodeFrontier rest3 frontier []
                          (by intro bs x hx; exact PublicFieldBlockCodec.encodeFrontier_of_decodeFrontier bs x hx)
                          hf
                      refine ⟨?_, ?_, ?_, ?_, ?_⟩
                      · simpa [hc] using (show anchor = anchor from rfl).symm
                      · simpa [hc] using (show nullifier = nullifier from rfl).symm
                      · simpa [hc] using (show assetId = assetId from rfl).symm
                      · simpa [hc] using (show change = change from rfl).symm
                      · rw [hiBytes, hsBytes, hrBytes, hfBytes]
                        simp [afterBytes, hc, List.append_assoc]
                  | cons byte tail => simp at h

private theorem decodeTransfer_sound (bytes : List Byte) (wire : Wire)
    (h : decodeTransfer bytes = some wire) :
    ∃ c recipient, wire = .transfer c recipient ∧ encode wire = 0 :: bytes := by
  unfold decodeTransfer at h
  cases ha : readDigest bytes with
  | none => simp [ha] at h
  | some ap =>
      rcases ap with ⟨anchor, rest1⟩
      simp [ha] at h
      cases hn : readDigest rest1 with
      | none => simp [hn] at h
      | some np =>
          rcases np with ⟨nullifier, rest2⟩
          simp [hn] at h
          cases hx : readField rest2 with
          | none => simp [hx] at h
          | some xp =>
              rcases xp with ⟨asset, rest3⟩
              simp [hx] at h
              cases ht : expect 1 rest3 with
              | none => simp [ht] at h
              | some rest4 =>
                  simp [ht] at h
                  cases hr : readDigest rest4 with
                  | none => simp [hr] at h
                  | some rp =>
                      rcases rp with ⟨recipientRead, rest5⟩
                      simp [hr] at h
                      cases hc : readDigest rest5 with
                      | none => simp [hc] at h
                      | some cp =>
                          rcases cp with ⟨changeRead, rest6⟩
                          simp [hc] at h
                          cases hz : expect 0 rest6 with
                          | none => simp [hz] at h
                          | some rest7 =>
                              simp [hz] at h
                              cases haft : decodeAfter anchor nullifier asset changeRead rest7 with
                              | none => simp [haft] at h
                              | some decoded =>
                                  simp [haft] at h
                                  cases wire with
                                  | transfer c recipient =>
                                    have hparts : decoded = c ∧ recipientRead = recipient := by
                                      simpa using h
                                    rcases hparts with ⟨hdecoded, hrecipient⟩
                                    subst decoded
                                    subst recipientRead
                                    rcases decodeAfter_sound anchor nullifier asset changeRead rest7 c haft with
                                      ⟨hanchor, hnullifier, hasset, hchange, hafter⟩
                                    have hAnchorBytes := PublicByteCursor.read_sound 32
                                      PublicFieldBlockCodec.decodeDigest PublicFieldBlockCodec.encodeDigest
                                      bytes anchor rest1
                                      (by intro bs x hx; exact PublicFieldBlockCodec.encodeDigest_of_decodeDigest bs x hx) ha
                                    have hNullifierBytes := PublicByteCursor.read_sound 32
                                      PublicFieldBlockCodec.decodeDigest PublicFieldBlockCodec.encodeDigest
                                      rest1 nullifier rest2
                                      (by intro bs x hx; exact PublicFieldBlockCodec.encodeDigest_of_decodeDigest bs x hx) hn
                                    have hAssetBytes := PublicByteCursor.read_sound 4
                                      ExactLeafFieldCodec.decodeM31 ExactLeafFieldCodec.encodeM31
                                      rest2 asset rest3
                                      (by intro bs x hx; exact ExactLeafFieldCodec.encodeM31_of_decodeM31 bs x hx) hx
                                    have hRecipientBytes := PublicByteCursor.read_sound 32
                                      PublicFieldBlockCodec.decodeDigest PublicFieldBlockCodec.encodeDigest
                                      rest4 recipient rest5
                                      (by intro bs x hx; exact PublicFieldBlockCodec.encodeDigest_of_decodeDigest bs x hx) hr
                                    have hChangeBytes := PublicByteCursor.read_sound 32
                                      PublicFieldBlockCodec.decodeDigest PublicFieldBlockCodec.encodeDigest
                                      rest5 changeRead rest6
                                      (by intro bs x hx; exact PublicFieldBlockCodec.encodeDigest_of_decodeDigest bs x hx) hc
                                    have hSep1 : rest3 = 1 :: rest4 := expect_sound 1 rest3 rest4 ht
                                    have hSep0 : rest6 = 0 :: rest7 := expect_sound 0 rest6 rest7 hz
                                    have hrest : bytes = header c ++ [1] ++
                                      PublicFieldBlockCodec.encodeDigest recipient ++
                                      PublicFieldBlockCodec.encodeDigest c.change ++ [0] ++ afterBytes c := by
                                      rw [hAnchorBytes, hNullifierBytes, hAssetBytes, hSep1,
                                        hRecipientBytes, hChangeBytes, hSep0, hafter]
                                      rw [← hanchor, ← hnullifier, ← hasset, ← hchange]
                                      simp only [header, List.append_assoc]
                                      simp only [List.singleton_append]
                                    refine ⟨c, recipient, rfl, ?_⟩
                                    simpa [encode] using
                                      (congrArg (fun xs : List Byte => 0 :: xs) hrest).symm
                                  | withdrawal c amount => cases h

private theorem decodeWithdrawal_sound (bytes : List Byte) (wire : Wire)
    (h : decodeWithdrawal bytes = some wire) :
    ∃ c amount, wire = .withdrawal c amount ∧ encode wire = 1 :: bytes := by
  unfold decodeWithdrawal at h
  cases ha : readDigest bytes with
  | none => simp [ha] at h
  | some ap =>
      rcases ap with ⟨anchor, rest1⟩
      simp [ha] at h
      cases hn : readDigest rest1 with
      | none => simp [hn] at h
      | some np =>
          rcases np with ⟨nullifier, rest2⟩
          simp [hn] at h
          cases hx : readField rest2 with
          | none => simp [hx] at h
          | some xp =>
              rcases xp with ⟨asset, rest3⟩
              simp [hx] at h
              cases hz : expect 0 rest3 with
              | none => simp [hz] at h
              | some rest4 =>
                  simp [hz] at h
                  cases hc : readDigest rest4 with
                  | none => simp [hc] at h
                  | some cp =>
                      rcases cp with ⟨changeRead, rest5⟩
                      simp [hc] at h
                      cases ht : expect 1 rest5 with
                      | none => simp [ht] at h
                      | some rest6 =>
                          simp [ht] at h
                          cases hm : readField rest6 with
                          | none => simp [hm] at h
                          | some mp =>
                              rcases mp with ⟨amountRead, rest7⟩
                              simp [hm] at h
                              cases haFt : decodeAfter anchor nullifier asset changeRead rest7 with
                              | none => simp [haFt] at h
                              | some decoded =>
                                  simp [haFt] at h
                                  cases wire with
                                  | withdrawal c amount =>
                                    have hparts : decoded = c ∧ amountRead = amount := by
                                      simpa using h
                                    rcases hparts with ⟨hdecoded, hamount⟩
                                    subst decoded
                                    subst amountRead
                                    rcases decodeAfter_sound anchor nullifier asset changeRead rest7 c haFt with
                                      ⟨hanchor, hnullifier, hasset, hchange, hafter⟩
                                    have hAnchorBytes := PublicByteCursor.read_sound 32
                                      PublicFieldBlockCodec.decodeDigest PublicFieldBlockCodec.encodeDigest
                                      bytes anchor rest1
                                      (by intro bs x hx; exact PublicFieldBlockCodec.encodeDigest_of_decodeDigest bs x hx) ha
                                    have hNullifierBytes := PublicByteCursor.read_sound 32
                                      PublicFieldBlockCodec.decodeDigest PublicFieldBlockCodec.encodeDigest
                                      rest1 nullifier rest2
                                      (by intro bs x hx; exact PublicFieldBlockCodec.encodeDigest_of_decodeDigest bs x hx) hn
                                    have hAssetBytes := PublicByteCursor.read_sound 4
                                      ExactLeafFieldCodec.decodeM31 ExactLeafFieldCodec.encodeM31
                                      rest2 asset rest3
                                      (by intro bs x hx; exact ExactLeafFieldCodec.encodeM31_of_decodeM31 bs x hx) hx
                                    have hChangeBytes := PublicByteCursor.read_sound 32
                                      PublicFieldBlockCodec.decodeDigest PublicFieldBlockCodec.encodeDigest
                                      rest4 changeRead rest5
                                      (by intro bs x hx; exact PublicFieldBlockCodec.encodeDigest_of_decodeDigest bs x hx) hc
                                    have hAmountBytes := PublicByteCursor.read_sound 4
                                      ExactLeafFieldCodec.decodeM31 ExactLeafFieldCodec.encodeM31
                                      rest6 amount rest7
                                      (by intro bs x hx; exact ExactLeafFieldCodec.encodeM31_of_decodeM31 bs x hx) hm
                                    have hSep0 : rest3 = 0 :: rest4 := expect_sound 0 rest3 rest4 hz
                                    have hSep1 : rest5 = 1 :: rest6 := expect_sound 1 rest5 rest6 ht
                                    have hrest : bytes = header c ++ [0] ++
                                      PublicFieldBlockCodec.encodeDigest c.change ++ [1] ++
                                      ExactLeafFieldCodec.encodeM31 amount ++ afterBytes c := by
                                      rw [hAnchorBytes, hNullifierBytes, hAssetBytes, hSep0,
                                        hChangeBytes, hSep1, hAmountBytes, hafter]
                                      rw [← hanchor, ← hnullifier, ← hasset, ← hchange]
                                      simp only [header, List.append_assoc]
                                      simp only [List.singleton_append]
                                    refine ⟨c, amount, rfl, ?_⟩
                                    simpa [encode] using
                                      (congrArg (fun xs : List Byte => 1 :: xs) hrest).symm
                                  | transfer c recipient => cases h

theorem encode_of_decode (bytes : List Byte) (wire : Wire)
    (h : decode bytes = some wire) : encode wire = bytes := by
  cases bytes with
  | nil => simp [decode] at h
  | cons tag rest =>
      change (if tag = 0 then decodeTransfer rest
        else if tag = 1 then decodeWithdrawal rest else none) = some wire at h
      by_cases hzero : tag = 0
      · simp [hzero] at h
        obtain ⟨c, recipient, hwire, hbody⟩ := decodeTransfer_sound rest wire h
        rw [hwire]
        have hbody' : encode (.transfer c recipient) = 0 :: rest := by
          simpa [hwire] using hbody
        simpa [hzero] using hbody'
      · by_cases hone : tag = 1
        · simp [hone] at h
          obtain ⟨c, amount, hwire, hbody⟩ := decodeWithdrawal_sound rest wire h
          rw [hwire]
          have hbody' : encode (.withdrawal c amount) = 1 :: rest := by
            simpa [hwire] using hbody
          simpa [hzero, hone] using hbody'
        · simp [hzero, hone] at h

#print axioms decodeAfter_sound
#print axioms encode_of_decode
end AspisR1.SemanticPublicWireSound
