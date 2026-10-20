> R1 update (2026-10-20): the R1 pair-forest marker path is no longer the
> nullifier-marker PDA path described below. B1 uses `create_with_seed` under
> the forest master; see [the accepted B1 review](LEAD-REVIEW-POOL-B1-20261019.md)
> and its freshness premise. Historical results and legacy PDA routes are unchanged.

# Pool PDA searches: design study (2026-10-19)

Mandate: `LEAD-DECISION-POOL-PDA-20261019.md` (user decision, option C).
Base: research `bb134241e`. Evidence: `../evidence/pool-pda-20261019/`.
Labels: **[measured]** LiteSVM/native measurement; **[analytical]** derived
from source and the Agave 4.2.1 cost schedule; **[proposed]** not implemented.

## 1. Inventory and classification of the settlement-route PDA derivations

Route: `process_pair_forest_terminal_with_verifier_v1`
(`programs/aspis-pool/src/pair_forest.rs:1396`), built with
`r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit`
as in every saved fixture. The registry branch is the immutable-deployment
(V2) branch, because the fixtures' policy sets
`POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT`. Order of execution and
line numbers are at `bb134241e`. "Constant" means the seeds are fixed once the
deployment (program id, mint, registry, selected release) is fixed;
"per-transaction" means the seeds vary from one settlement to the next.

| # | Call site | Seeds (program) | Class | What the program relies on |
|---|---|---|---|---|
| 1 | `decode_master_account` `pair_forest.rs:335` | `aspis-pair-forest-master-v1`, mint (Pool) | constant | authenticity of the one forest master per mint; bump stored at byte 7 since G_R1.8 |
| 2 | `decode_retained_pair_forest_checkpoint_account_v1` `pair_forest.rs:1966` | `...-checkpoint-v1`, master, sequence (Pool) | per-transaction (the spender picks the retained anchor) | authenticity of an existing immutable checkpoint; bump stored at byte 7 |
| 3 | `decode_lane_account[_from_program_invariant_v1]` `pair_forest.rs:353/386` | `...-lane-v1`, master, lane id (Pool) | constant (8 accounts; lane id = f(nullifier)) | authenticity; bump stored at byte 72 |
| 4 | `validate_pair_forest_request_accounts_v1` `pair_forest.rs:1152` | same as 3 | constant | same as 3; repeats the check of row 3 for the same key |
| 5 | `require_root_page_address` (`history.rs:85`, from `pair_forest.rs:1046` or `:651`) | `aspis-pool-root-page-v1`, lane, page number (Pool) | per-transaction (page = lane position >> 8) | authenticity of the existing current page; the page image stores no bump |
| 6 | rollover only, `pair_forest.rs:1061` | same as 5, page + 1 | per-transaction | the next page must be a zeroed Pool-owned account at the canonical address |
| 7 | `plan_nullifier_marker_consumption_v1` (`nullifier.rs:32`) | `aspis-pool-nullifier-v1`, master, nullifier (Pool) | per-transaction | **uniqueness**: one marker address per nullifier; the account is created in this transaction |
| 8 | replan in `create_nullifier_marker_if_needed_v1` (`processor.rs:1535`) | same as 7 | per-transaction | same as 7; repeats row 7's search for the same seeds |
| 9 | `authenticate_verifier_selection_v2` `registry.rs:278` | registry program id (BPF loader upgradeable) | constant | registry image binds the registry's programdata address |
| 10 | `registry.rs:283` | `aspis-verifier-registry-v2`, master (registry program) | constant | authenticity of the registry account; bump stored by the registry program |
| 11 | `registry.rs:305` | `aspis-verifier-entry-v2`, master, profile, release (registry program) | constant per selected release | authenticity of the entry; bump stored |
| 12 | `registry.rs:329` | verifier program id (loader) | constant | entry binds the verifier's programdata address; `programdata_bump` stored |
| 13 | withdrawal, `vault.rs:446` | `aspis-pool-vault-authority-v1`, master (Pool) | constant | **signing authority** for the SPL `TransferChecked` (`invoke_signed`, `pair_forest.rs:1557`) |
| 14 | withdrawal, `vault.rs:468` | `aspis-pool-vault-token-v1`, master (Pool) | constant | authenticity of the custody token account |

Counts: transfer 11 (genesis or same page) or 12 (rollover); withdrawal 13 or
14. These equal the traced `sol_try_find_program_address` counts in
`cu-bound-20261019` (`[11, 12, 12, 11, 11, 11]` per transfer trace; 13-14 per
withdrawal), so the list is complete for this route.

Account-creation paths the settlement depends on:

- **Nullifier marker**: created inside the settlement (rows 7-8), System
  `create_account` (or transfer+allocate+assign if prefunded) under
  `invoke_signed` with the bump from row 7. This is the only PDA whose
  *uniqueness*, not just authenticity, is a soundness property: a second
  Pool-owned marker for the same nullifier at a different address would let
  the same note be spent twice.
- **Checkpoint**: created by the separate checkpoint instruction
  (`plan_pair_forest_checkpoint_accounts_v1`, `pair_forest.rs:585`), seeds
  from `master.next_checkpoint_sequence` (state, not caller-chosen), one search
  per checkpoint, outside the settlement.
- **Root pages**: created by deposits at page 0 and on deposit rollover
  (`pair_forest.rs:846,874`); a spend rollover requires an already zeroed
  Pool-owned page (row 6; the measurement driver injects it).
- **Master, lanes**: created once by `process_pair_forest_initialize_with_runtime_v1`
  (`pair_forest.rs:1778,1792`) at the canonical bumps.
- **Registry, entry**: created by `programs/aspis-registry`
  (`processor.rs:934,1023`) at the canonical bumps, which its decoder
  re-checks (`processor.rs:462-466,502-505`).

Every `invoke_signed` in `programs/aspis-pool` signs with a bump that came
from `find_program_address` in the same instruction (master/lane init, page,
checkpoint, marker, vault authority). The Pool therefore never signs for a
non-canonical address, and every Pool-owned account at a PDA address sits at
the canonical bump. This is the premise on which a stored bump is enough to
authenticate an *existing* account (section 2).

Not on this route: `pool_v1_state_address` (`state.rs:50`) and
`pool_v1_pair_state_address` (`pair_state.rs:63`) belong to the legacy
single-tree and pair routes; the prepared-settlement addresses
(`prepared_settlement_format.rs:231,247`, `prepared_settlement.rs:232`) and
the V1 (mutable) registry branch (`registry.rs:186,212`) are not executed by
the R1 settlement. They are left unchanged.

## 2. Runtime facts used by every option

All from the Agave 4.2.1 sources in the build host's cargo registry
(`solana-syscalls-4.2.1`, `solana-program-runtime-4.2.1`,
`solana-address-2.6.1`, `solana-curve25519-4.0.1`, `agave-feature-set-4.2.1`).

F1. **`sol_try_find_program_address`** (`solana-syscalls/src/lib.rs:884-929`)
charges `create_program_address_units = 1500` once, then tries bumps 255, 254,
..., 1 (at most 255 attempts; bump 0 is never tried) and charges another 1,500
after each failed attempt. A search that succeeds on attempt k costs exactly
**1,500·k CU**; the most expensive accepted search costs 382,500 CU; a search
that fails all 255 attempts costs 384,000 CU and returns an error.

F2. **`sol_create_program_address`** (`lib.rs:843-879`) charges 1,500 once and
performs one attempt with the caller's bump.

F3. **Off-curve predicate.** An attempt succeeds iff
`SHA-256(seeds ‖ bump ‖ program_id ‖ "ProgramDerivedAddress")` is *not* a
point: `CompressedEdwardsY::from_slice(h).decompress().is_some()` is false
(`solana-address/src/lib.rs:188-198`, `syscalls.rs:396-422`). The
`sol_curve_validate_point` syscall for `CURVE25519_EDWARDS` evaluates the
**same expression** (`solana-curve25519/src/edwards.rs:77-85`, syscall
`lib.rs:1000-1043`) and costs `curve25519_edwards_validate_point_cost = 159`.
It is behind `curve25519_syscall_enabled`
(`7rcw5UtqgDTBBv2EcynNfYckgdAaH1MAsCjKgXMkN7Ri`), which a read of the feature
account on 2026-10-19 shows activated on mainnet-beta at slot 275,184,000
and on devnet at slot 240,192,004 (RPC `getAccountInfo`, `apiVersion`
4.3.0 and 4.4.0-beta.0 respectively).

F4. **Off-curve rate [measured].** Decompression succeeds iff
(y²−1)/(d·y²+1) is a square mod p = 2²⁵⁵−19, which holds for about half of
the field elements y; SHA-256 outputs give y uniform up to the masked sign
bit, so each attempt is off-curve with probability close to 1/2, independent
across bumps (distinct hash inputs). Measured with the Pool's own
`solana-pubkey 2.4.0` (native `curve25519-dalek 4.1.3`, the same
`decompress` predicate), `evidence/pool-pda-20261019/offcurve/`:

| Sample | Size | Off-curve |
|---|---:|---:|
| raw SHA-256 outputs | 1,000,000 | 0.500390 |
| marker-shaped PDA candidates (`aspis-pool-nullifier-v1`, pool, random nullifier) | 2,000,378 candidates over 10⁶ searches | 0.499906 |

The attempt histogram for 10⁶ searches is geometric: 499,906 / 249,913 /
125,144 / 62,548 / 31,194 needed 1-5 attempts, the maximum was 21, and
P(k > j) tracks 2⁻ʲ for every j ≤ 17 to within sampling error
(`offcurve-result.json`). Below, P(k > j) = 2⁻ʲ is used.

F5. **SHA-256 syscall** (`lib.rs:2542-2598`): 85 CU plus, per slice,
max(10, ⌊len/2⌋).

F6. **Stored bumps for existing accounts.** For an account that already
exists, `key == create_program_address(seeds ‖ stored_bump)` together with
`owner == program` authenticates it if every account the program owns at a
PDA of those seeds sits at the canonical bump. That holds in Pool because the
Pool only signs (`invoke_signed`) with bumps returned by
`find_program_address` (section 1), and nobody else can allocate or assign an
account at a PDA address. The check does **not** establish canonicality by
itself: natively, a Pool-owned image at a non-canonical address with a
matching stored bump is accepted. This is the same premise G_R1.8 used for
the verifier adapter (the "program-owned data is written only by admitted
routes" premise of G_R1.9 / J1.R15). For a PDA that is **created** in the
transaction (the nullifier marker), no stored bump exists yet, and a
caller-supplied bump is not enough: the Pool would sign for whatever bump it
is given, so uniqueness then needs the canonical search or another argument.

## 3. Option A: canonical search with a tail rule

**Rule.** Keep `find_program_address` for the per-transaction seeds (rows 2,
5, 6, 7, 8) and state the CU bound as a probability: a settlement exceeds a
limit L with probability P_L per note, computed below. Rows 1, 3, 4, 9-12 use
stored bumps after Part 2 (section 7); rows 13-14 (vault) remain searches with
constant seeds, so their cost is fixed per deployment and is part of the
base.

**Attempt distribution.** By F1 and F4 a search succeeds on attempt k with
probability 2⁻ᵏ (k = 1..255) and costs 1,500·k CU, i.e. 1,500·(k−1) more than
the one-attempt path. P(k > j) = 2⁻ʲ. The two marker searches (rows 7 and 8)
use the same seeds and therefore the same k, so the marker contributes
3,000·(k−1). Checkpoint, current page and (on rollover) next page are
independent draws.

| extra attempts on one search | extra CU | P(at least this many) |
|---:|---:|---:|
| 1 | 1,500 | 1/2 |
| 10 | 15,000 | 2⁻¹⁰ ≈ 9.8·10⁻⁴ |
| 20 | 30,000 | 2⁻²⁰ ≈ 9.5·10⁻⁷ |
| 32 | 48,000 | 2⁻³² ≈ 2.3·10⁻¹⁰ |
| 64 | 96,000 | 2⁻⁶⁴ ≈ 5.4·10⁻²⁰ |
| 254 (max accepted) | 381,000 | 2⁻²⁵⁴ |

**Base.** Settlement CU with one attempt on every remaining per-transaction
search is not measured directly. As base I use the cu-bound **random-sweep
maxima** (1,192,252 transfer, 1,206,877 withdrawal [swept]) minus the Part 2
saving (4,123 [measured]): 1,188,129 and 1,202,754. These are upper bounds on
the zero-extra-attempt base only up to sampling (the sweep's maxima already
contain whatever extra attempts those runs drew); they are **not** worst-case
bounds. Under the pre-registered analytical method the non-search part of
B_settlement is 1,632,876 / 1,652,751 [analytical, cu-bound REPORT §4], so no
tail rule on the bump searches can by itself turn that method's verdict into
PASS; option A only bounds the bump term.

**Exact tails [analytical]** (`evidence/pool-pda-20261019/tail-result.json`,
`harness/tail.py`, exact rational convolution of the geometric laws, 255-attempt
cap):

| Search set | T > 1.3M | T > 1.4M | W > 1.3M | W > 1.4M |
|---|---:|---:|---:|---:|
| current (checkpoint, page, marker ×2) | 1.3·10⁻¹¹ (2⁻³⁶·²) | 1.1·10⁻²¹ (2⁻⁶⁹·⁷) | 4.1·10⁻¹⁰ (2⁻³¹·²) | 3.4·10⁻²⁰ (2⁻⁶⁴·⁷) |
| current, rollover (+ next page) | 2.2·10⁻¹¹ | 1.8·10⁻²¹ | 7.0·10⁻¹⁰ | 5.8·10⁻²⁰ |
| marker searched once (pass row 7's bump to row 8) | 2.0·10⁻²⁰ | 4.7·10⁻⁴⁰ | 1.5·10⁻¹⁷ | 4.2·10⁻³⁷ |
| marker once + checkpoint by stored bump | 1.0·10⁻²¹ | 1.3·10⁻⁴¹ | 9.1·10⁻¹⁹ | 1.2·10⁻³⁸ |

The allowed extra attempts are ⌊(L − base)/1,500⌋: 74 (T, 1.3M), 141 (T,
1.4M), 64 (W, 1.3M), 131 (W, 1.4M). With the current code a withdrawal
exceeds 1.3M for about one note in 2.5·10⁹ and the 1.4M transaction cap for
about one in 3·10¹⁹.

**Consequence of a tail event.** Above 1.3M and at or below 1.4M the
settlement still executes; only the CU target is missed. Above 1.4M the
transaction cannot execute. Which factor caused it matters:

- *Marker* (rows 7-8): the seeds are (tag, master, nullifier) and the
  nullifier is `derive_nullifier(nullifier_key, salt)` (`format.rs:235`),
  fixed when the note is created. The spender cannot change it: the output lane
  is also a function of the nullifier, the master is the deployment's, and the
  transfer sender who chose the salt does not know the recipient's
  nullifier key, so nobody can grind it. Such a note is **permanently
  unspendable** under this program (the value stays in the vault) unless a
  program upgrade adds a route. The depositor of a self-owned note could grind
  its own salt; nothing in the protocol asks for that.
- *Checkpoint* (row 2): the spender picks the retained anchor; any other
  admissible checkpoint has independent seeds, so this is recoverable by
  choosing another anchor (or waiting for the next checkpoint).
- *Pages* (rows 5-6): fixed by the lane position; recoverable after the
  lane's position moves to the next page, i.e. after up to 256 further
  appends on that lane, but every note spent on that lane meanwhile pays it.

**Adversary.** Nobody can choose another user's marker seeds. An adversary can
create checkpoints (seeds are state-determined sequence numbers) and advance
lane positions, but cannot select bumps except by waiting, and every tail
event it waits for costs it real appends. The 2⁻ʲ law therefore holds for
honest notes; a self-ground note only hurts its owner.

**Cost of option A.** No code beyond what exists; no migration; no Lean change
(the address function and the freshness premise are unchanged). The release
claim becomes probabilistic: "settlement ≤ L except with probability P_L per
note", with P_L from the table, plus the runtime premise F1/F4. Two cheap
source improvements shrink the tail without changing any address: pass the
marker bump from the plan to the replan (rows 7-8 become one search;
2⁻³¹ → 2⁻⁵⁶ for W at 1.3M) and authenticate the existing checkpoint by its
stored bump (already done by the verifier adapter).

## 4. Option B: search-free or bounded designs

Common ground for every B option: the verifier CPI account list is
`[proof, master, Pool checkpoint, lane, registry, entry, R1 checkpoint]`
(G_R1.9); the marker and the history pages are not passed to the verifier, and
the R1 statement carries the nullifier as a public value only. So **no B
option changes the R1 verifier, the adapter or its CPI interface**; what
changes is how the Pool records "this nullifier is spent". In the J1 documents
(`J1-RELATION-STATEMENT-20261015.md`), `Rspend` and `SpendAppendBinding` are
statements about the proof relation and do not mention the marker address;
nullifier freshness is listed as a separate release gate. That gate (and any
account-history premise that names the marker PDA) is what an address change
would restate.

**Live accounts.** J1.R19 records that no deployment exists for the R1 Pool
route. The only mainnet Aspis execution (`docs/mainnet-demo.md`, 2026-07-16)
used a disposable earlier program id
(`GQPNqfYF17Nj2dGsf6Q2AtiouyM67YxFZPh9LxBk2Ye3`) whose ProgramData was
closed after the demonstration; its pool and marker accounts remain on chain
but cannot be used by any current program. I found no devnet deployment of
the pair-forest Pool in `docs/`. So every B option has **no data migration**;
it is a format change for the release.

### B1. `create_with_seed` marker address

Address = SHA-256(base ‖ seed ‖ owner) (`Pubkey::create_with_seed`), with
owner = Pool, base = a fixed per-pool Pool PDA ("marker authority", seeds
`[tag, master]`, bump stored in the master or computed once at
initialization) that signs `create_account_with_seed` /
`allocate_with_seed` / `assign_with_seed` through `invoke_signed`. No curve
check is involved, so there is no bump and no search.

*Seed encoding.* The System program takes the seed as a `String` of at most 32
bytes (`MAX_SEED_LEN`) and rejects invalid UTF-8 at deserialization. UTF-8
carries at most 7 bits per byte in this length budget (ASCII; multi-byte
sequences carry 5.5, 5.33 or 5.25 bits per byte), so 32 bytes hold at most 224
bits, less than the nullifier's 8 × 31 = 248 bits. The nullifier therefore
cannot be encoded injectively; the seed must be a 224-bit digest:
seed = 7-bit packing of the first 28 bytes of SHA-256("aspis-marker-seed-v1"
‖ pool ‖ nullifier), every byte in 0x00-0x7f (valid UTF-8, exactly 32 bytes).
The owner must not end with the PDA marker (the Pool id does not).

*Uniqueness / double spend.* The Pool computes the seed itself from the
nullifier, so one nullifier gives exactly one address: there is no free
parameter like a bump, and the adversary cannot create a second valid record
for the same nullifier. A second account at the same address is impossible
(the address is one account), and an account at that address can only be
created with the base's signature, i.e. by the Pool. A different nullifier
mapping to the same seed is a 224-bit truncated-hash collision: a *birthday*
collision (≈2¹¹² work) among the attacker's own notes only makes one of its
own notes unspendable; making a **victim's** note unspendable needs a second
preimage of the victim's seed (≈2²²⁴) and the victim's nullifier, which is
public only when it is spent. Cross-domain collisions with Pool PDAs need a
SHA-256 collision (different input formats: PDA hashes end in
`"ProgramDerivedAddress"`). No double spend arises from any collision: a
collision can only make a marker *look* used.

*CU [analytical].* SHA-256 of (domain 20 B, pool 32 B, nullifier 32 B) =
85 + 10 + 16 + 16 = 127; packing 32 bytes ≈ 100 SBF instructions; the address
SHA-256 (base 32, seed 32, owner 32) = 85 + 3·16 = 133. About **360 CU,
deterministic**, replacing 2 × 1,500·k. The marker creation CPI is the same
System call with a seed argument (≈40 more instruction-data bytes).
Rent is unchanged (same 208-byte account).

*Changes.* Pool: marker address function, the System instruction variants
(`create_account_with_seed`, and `transfer` + `allocate_with_seed` +
`assign_with_seed` for a prefunded address), a marker-authority PDA in the
master or a new constant-seed account. Clients and the wallet derive the new
address. Lean/soundness: the freshness gate is restated with the new address
function and a named collision-resistance premise for the truncated SHA-256
(currently freshness needs no hash premise beyond the PDA syscall).

### B2. Nullifier pages (sorted pages or bitmaps)

A bitmap indexed by nullifier is impossible (2²⁴⁸ entries). The workable form
is a fixed set of 2ᵖ Pool-owned pages, page = top p bits of the nullifier,
created at initialization at canonical bumps and authenticated by stored
bump (F6), each holding a sorted array of 32-byte nullifiers. Membership is a
binary search; insertion shifts the tail of the array.

*Uniqueness.* Each nullifier belongs to exactly one page and the page is the
single canonical account for its prefix, so a spend is unique iff the
nullifier is not in that page; there is no address freedom at all.

*CU [analytical].* Search ≤ ⌈log₂ n⌉ 32-byte comparisons (a few hundred CU);
insertion moves up to 32·n bytes (`sol_memmove` = max(10, len/250) CU: a
1 MiB page costs up to ≈4.2k CU, a 10 MiB page ≈42k), deterministic in the
page size. The pages must be loaded (and write-locked) by every spend.

*Costs and risks.* Storage: 32 B per nullifier instead of a 336-byte account
(about 10× less rent per note), but the pages are paid up front (≈7 SOL per
MiB rent-exempt). Capacity is the hard problem: an adversary with many notes
can grind its own salts into one prefix and fill a page, blocking every honest
note with that prefix until overflow handling exists, and overflow chains make
the CU depend on adversarial chain length again. All spends with the same
prefix serialize on one write lock. Account growth is limited to 10 KiB per
instruction by `realloc`.

*Changes.* New page format, initialization of 2ᵖ accounts, a new spend
account list, removal of the marker, client indexing of pages. Lean: the
freshness gate becomes "nullifier ∉ page(prefix)" with an inductive page
invariant (sorted, prefix-correct, written only by the spend route), a larger
restatement than B1.

### B3. Bounded canonical search done by the program (same addresses)

Keep the canonical marker address and compute it inside the program:
for bump = 255 down to 1, h = `sol_sha256`(seeds ‖ bump ‖ program_id ‖
"ProgramDerivedAddress"); stop at the first h for which
`sol_curve_validate_point(CURVE25519_EDWARDS, h)` reports "not a point". By F3
this is exactly the runtime's `find_program_address`: same hash, same
`decompress().is_some()` predicate, same order, so it yields the same
canonical address and bump, and `invoke_signed` with that bump then creates
the marker as today.

*Uniqueness.* Unchanged: the address is the canonical PDA. The only new
premise is F3 (the validate syscall evaluates the same predicate as
`sol_create_program_address`, and `curve25519_syscall_enabled` is active on the
target cluster; both checked for Agave 4.2.1 and mainnet/devnet on
2026-10-19).

*CU [analytical].* Per attempt: SHA-256 of (23, 32, 32, 1, 32, 21 bytes) =
85 + 11 + 16 + 16 + 10 + 16 + 10 = 164; validate 159; loop and syscall
argument setup, estimated ≤ 60 instructions: **≤ ≈385 CU per attempt** against
1,500. Worst case 255 attempts ≈ 98k CU per search (deterministic bound),
expected ≈ 770. Done once (no replan search), the marker term is bounded by
≈98k instead of 2 × 382,500. The estimate needs one measurement before it is
relied on.

*Changes.* Pool only (marker derivation and the replan); no format, address,
client, migration or Lean change beyond naming F3 as a runtime premise next
to the existing PDA premise (J1.R16 already pins `sol_sha256` and
`sol_create_program_address`; this adds `sol_curve_validate_point`).

### B4. Existing per-transaction accounts by stored bump or bump hint

Not a marker design but needed with every B option, since the marker is not
the only searched seed. The checkpoint already stores its bump (byte 7) and
the verifier adapter already authenticates it with one
`create_program_address`; the Pool can do the same (row 2). History pages
store no bump; because they already exist and the Pool created them at
canonical bumps, F6 makes a **caller-supplied bump hint** checked with one
`create_program_address` sound for rows 5-6 (an instruction-data change: two
bytes), or the page header can gain a bump byte (page format change). This is
**not** sound for the marker, which is created in the same transaction (F6).
With B4, rows 2, 5, 6 cost 1,500 each, deterministic.

## 5. Comparison

Marker term = the nullifier-marker part of the settlement's PDA cost; the
other per-transaction searches (checkpoint, pages) are listed separately
because B4 removes them for any marker choice.

| | A: search + tail rule | A + dedupe + B4 | B1: `create_with_seed` | B2: nullifier pages | B3: in-program bounded search (+B4) |
|---|---|---|---|---|---|
| Marker worst case | 765,000 (2 × 382,500), P(>1.4M) ≈ 3·10⁻²⁰ (W) | 382,500, P(>1.4M) ≈ 1.8·10⁻⁴⁰ (W, marker the only search) | ≈360, deterministic | log-search + memmove ≤ ≈4-42k, deterministic in page size | ≤ ≈98k, deterministic (estimate) |
| Checkpoint + pages | up to 3 × 382,500, probabilistic | 3 × 1,500 | needs B4 | needs B4 | 3 × 1,500 |
| Deterministic CU bound | no | no | yes (with B4) | yes, but page size enters | yes (with B4) |
| Double-spend argument | canonical bump (search) | same | address is a function of the nullifier; no free parameter | one page per prefix; set membership | canonical bump, identical addresses |
| New premise | F1/F4 tail law | same | truncated-SHA-256 collision resistance (DoS only) | page invariants | F3: `sol_curve_validate_point` ≡ PDA predicate |
| Stuck-note risk | ≈4·10⁻¹⁰ per withdrawal above 1.3M, ≈3·10⁻²⁰ above 1.4M | ≈2.7·10⁻²⁰ / 1.8·10⁻⁴⁰ (W) | none from CU; 2⁻²²⁴ second-preimage DoS | adversarial page filling | none from CU |
| Rent per note | 336-byte marker | same | same | 32 B (+ pages up front) | same |
| Migration | none | none | none (no live accounts) | none, but new initialization | none |
| Format / client change | none | page hint bytes (or page bump byte) | marker address, System instruction, authority PDA | new accounts, account list | page hint bytes (or page bump byte) |
| Verifier / adapter change | none | none | none | none | none |
| Lean / soundness restatement | probabilistic CU claim | same | freshness gate (address + hash premise) | freshness gate (set + page invariant) | runtime premise list only |

## 6. Recommendation (for the user to decide)

This is a recommendation only; the decision is the user's (option C).

I recommend **B3 with B4**: compute the canonical marker PDA inside the Pool
with `sol_sha256` + `sol_curve_validate_point` (once per settlement), and
authenticate the existing checkpoint and history pages by stored bump or a
checked bump hint. It keeps every address, format and the uniqueness
argument exactly as they are, needs no migration, client-visible change is at
most two hint bytes, and it turns the bump term into a deterministic bound
(≈98k CU worst case for the marker, 1,500 for each existing account, to be
confirmed by one measurement), at the price of one more named runtime
premise (F3). B1 is the fallback if a deterministic bound well below 98k is
needed: it is the cheapest (≈360 CU) and has a clean uniqueness argument, but
it changes the marker address scheme and adds a hash premise to the freshness
gate. Option A is acceptable only if a probabilistic CU claim is acceptable to
the user; if it is kept, the marker should at least be searched once (dedupe)
and the checkpoint authenticated by its stored bump, which costs nothing in
format or soundness. B2 is not recommended: its capacity and adversarial
filling problems reintroduce adversary-dependent cost.

None of these options addresses the non-search part of the first method's
bound (1.63M); that is for the separately pre-registered second bound.

## 7. Part 2 result: stored canonical bumps for constant-seed Pool PDAs

Implemented in `89396ac56` (`programs/aspis-pool/src/pair_forest.rs`,
`registry.rs`), following G_R1.8: one `create_program_address` with the
stored bump, ownership/signer/writability checks unchanged, rejection paths
fall back to the canonical search only to keep the previous error codes.

| Row | Site | Bump source | Changed |
|---|---|---|---|
| 1 | master | master byte 7 (G_R1.8) | yes |
| 3, 4 | lane (both checks) | lane byte 72 (G_R1.8) | yes |
| 9 | registry programdata | registry V2 `programdata_bump` | yes |
| 10 | registry V2 | registry V2 `bump` | yes |
| 11 | entry V2 | entry V2 `bump` | yes |
| 12 | verifier programdata | entry V2 `programdata_bump` | yes |
| 13, 14 | vault authority, vault token | **not stored anywhere** | no |
| — | `pool_v1_state_address`, `pool_v1_pair_state_address` | not on the R1 route | no |
| 2, 5-8 | checkpoint, pages, marker | per-transaction (mandate) | no |

The vault addresses (withdrawal only) are constant-seed, but neither the
master nor any other Pool-only account stores their bumps. Storing them needs
a master image change in `aspis-statement`, whose master decoder the R1
verifier also links (`r1_pool_adapter.rs` `decode_master_box`); that would
change the verifier ELF and its pins, which this job was not to do. Left open
for a lead decision (two reserved master bytes, or a Pool-only hint).

Measured on the six saved fixtures with the cu-bound driver, verifier
(`a70f30bd…`) and registry (`7ad46f0d…`) unchanged, Pool `b33302fd…` →
`f2a30ebc…` (589,256 bytes; clean rebuild byte-identical):

| Fixture | Stage 1 | Nested stage 2 | Settlement before | after | saved |
|---|---:|---:|---:|---:|---:|
| transfer 13 | 1,199,648 = | 1,034,767 = | 1,137,397 | 1,133,274 | 4,123 |
| transfer 255 | 1,199,567 = | 1,034,718 = | 1,174,671 | 1,170,548 | 4,123 |
| transfer 1023 | 1,199,687 = | 1,034,688 = | 1,171,579 | 1,167,456 | 4,123 |
| withdrawal 13 | 1,198,225 = | 1,034,510 = | 1,150,958 | 1,146,835 | 4,123 |
| withdrawal 255 | 1,198,264 = | 1,034,675 = | 1,188,496 | 1,184,373 | 4,123 |
| withdrawal 1023 | 1,198,386 = | 1,034,477 = | 1,185,236 | 1,181,113 | 4,123 |

In these fixtures three of the seven converted derivations needed two attempts
(master 254, entry 254, verifier programdata 254; the others 255), so 4,500
CU of searching was removed and the new code costs 377 CU of instructions
(inferred from the difference). The saving per deployment is
1,500·Σ(kᵢ−1) − 377 over the seven derivations; its worst case removes up to
7 × 381,000 CU of deployment-dependent cost from the bound.

Gates: SBF build (exit 0); Pool tests with the R1 feature set (111 passed),
default (84), V7 candidate aggregate (116), all features (116); exhaustive
native mutation tests (every wrong bump 0-255 for master, eight lanes, both
lane decoders, registry, entry and both programdata bumps; wrong key, wrong
lane id, wrong owner, signer; a forged registry image storing another off-curve
bump); SBF rejection runs `wrong-release` (Pool `InvalidVerifierEntryAddress`
on the new path), `stale-lane` and `replay` (second spend
`NullifierAlreadyConsumed`) for transfer and withdrawal; strict linked-ELF
stack audit on a clean build (28 frame and 23 overwrite diagnostics, all
absent from the linked ELF; gate pass). A recorded premise-boundary test shows
that, natively, a Pool-owned lane image at a non-canonical PDA with a matching
stored bump is accepted; on chain such an account cannot exist (F6).
Receipts: `evidence/pool-pda-20261019/receipts/`, `part2-result.json`.
