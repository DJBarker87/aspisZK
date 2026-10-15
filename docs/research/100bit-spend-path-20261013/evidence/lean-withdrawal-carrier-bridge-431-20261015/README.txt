Fixed withdrawal carrier bridge, Lean 4.31

Base 3c9db11a9748a2b7a1b3e96fabb19e24d4b106a4. Two new Lean files only;
no existing Rust/Lean or frozen PublicRawCore source changes.

The separately extracted serializer and validator PoolV1WithdrawalPublicV1
structures each contain the same nine fields. Their exact original Rust struct
fragments are byte-identical (SHA256 6b484d009350ba9f4dfb325e97c51c7370168b7cc5d7439a91d6df0b850278e4).
carrier-identity.json records the source paths. Both M31 aliases reduce to the
same backend U32 type. WithdrawalCarrier431.toValidator and fromValidator copy
pool, deployment_domain, anchor_sequence, anchor_root, nullifier, asset_id,
amount, destination_token_account and change_commitment explicitly. No field
is chosen from successful output and no modular reduction is used.

Checked in AspisR1PublicSerializer.WithdrawalCarrier431:
- from_to and to_from: both whole-structure roundtrips.
- toValidator_fields: simultaneous equality of all nine coordinates.
- HelperValidated p names only actual generated validator success on toValidator p.
- helper_success_amount_guard: that premise implies 0 < p.amount.val < 2^30.
- helper_success_raw_amount_guard/nonzero: for arbitrary unchanged transition t,
  the same premise supplies the pure guard/nonzero predicate on the existing
  RawBridge431.project (.Withdrawal p t).
- validated_source_success: actual helper success AND actual generated serializer
  success on that fixed public input imply the existing pure serialization result,
  its amount guard and its nonzero-withdrawal predicate.

PublicRawAmountGuard imports only PublicRawCore. Its two pure predicates match
the current PublicSourceRaw case definitions and remain available for a separate
4.32 check. The frozen source SHA256 is
5cdf46e38796664585f2dfca0284508fd59aae6ef37a5fe2f8312dcb7bdd8701.
Its nonzero_of_payment_guard theorem is axiom-free. That check does not import
or assert a 4.32 result here.

Focused first attempts both passed: pure guard 2.567 s, sampled group RSS
1,224,592 KiB; carrier bridge 13.971 s, 2,761,472 KiB. Process swap counts were
zero and recorded preexisting system swap was unchanged. Seven bridge axioms
reports contain only propext, Classical.choice and Quot.sound; the pure lemma
uses none. Source snapshots, exact receipts/logs, objects and eight audit results
are retained. Reused prerequisite source/object and backend reference hashes
were verified; Lean 4.31 version and binary/runtime dylib pins were observed again.
No generated source, unchanged module, native suite or dependency was rebuilt.

The runner uses lake env lean with the retained backend/overlay, -M6000 and
sampled 7 GiB process-group stop/180 s timeout. This is not a hard cgroup.
Absolute recorded paths describe the check environment and may need relocation.

OPEN: a successful actual verifier/caller reaching this validator on the mapped
input; ASF8/ASWP/late-record codec and omitted metadata transport; account,
checkpoint, hash and custody binding; extraction/compiler/runtime semantics;
and one-kernel integration with the existing 4.32 R1 development. The structural
carrier gap is addressed inside the checked 4.31 model. HelperValidated is not
silently promoted to verifier success or arbitrary SourceValidationAmountGuard.
