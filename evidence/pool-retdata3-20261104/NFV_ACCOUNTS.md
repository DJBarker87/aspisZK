# Account association under ruling (af)

Preparation; no new native credit yet. Frozen revision 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
The original NFO_read::association names are retained. Exact KMX patch:
bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.
AccountMeta layout: Pubkey [u8;32], two bool fields, byte alignment: 34 bytes.
Six entries copy 6*34=204 bytes; loop bound 204+1=205.
No NFR passing or timed-out configuration will be repeated unchanged.

NFV_K001: prescribed unwind205 stops on the reached KMX realloc loop,
not on a key assertion (exit1,98.696s,1345272KiB,swap0). The SAME caller
also constructs seven AccountInfo values and inserts the checkpoint. On the
host layout AccountInfo is 48 bytes, so its copied prefix is 7*48=336 and the
complete bound is max(204,336)+1=337. K002 changes only the insufficient
unwind bound; no timeout/cap increase or unchanged timed-out rerun.
The requested 205 arithmetic covers AccountMeta only and does not bound all
reached copies in this frozen caller. This discrepancy is recorded, not hidden.

The constructor fact named K057/K058 in (af) is **NFO_K057/NFO_K058**,
not NFR_K057/NFR_K058 (the latter are different settlement controls).
Flag and appended-element facts are NFR_K004/K005 and NFR_K006/K007.
These exact identifiers are retained to prevent an accidental evidence join.
NFV_B002 proves the list-level account order and readonly flags, with only
propext (flags) and no axioms (keys/account_order). B001 was a failed proof
edit and is not credited. No list value law proves native Vec realization.

Validation script change: campaign timeout detection now recognises the actual
lowercase "CBMC timed out" diagnostic. Earlier generated campaign rows were
recomputed from their immutable stdout. This changes reporting, not validation
conditions or any native verdict. Allocator source excerpts are suppressed in
runner summaries; full raw logs stay in evidence.

## Terminal account disposition

**AccountMeta: CLOSED-BY-RECLASSIFICATION under (af)(3).**
**AccountInfo: CLOSED-BY-RECLASSIFICATION under (af)(3).**
All24 full per-index positives/controls are terminal90s solver timeouts, not
passes or failing-control certificates. Eight stricter byte-observation splits
also time out (K003..007,K035..037). No shape was rerun unchanged after timeout.
No copied-prefix native pass credit is claimed. NFV_AF_CERTIFICATE.json checks
each immutable receipt and records the source of every fact.

The native certificate is NFO_K057/K058 constructors; NFR_K004/K005 flags;
NFR_K006/K007 lengths/appended metadata; and NFV_K008/K009 inserted Info key6.
K010 proves host layouts34/48, K011 corrupt-size control fails. Standard-library
push/insert preservation, including shifting the verifier-program element, is
retained std/allocator realization trust under P6/D188 option A. This is a
RECLASSIFICATION, never removal, and adds no trust row. The old K-1c classification
is retained; no shipped Pool bug or new fidelity defect is claimed.

The prescribed205 bound was tested and is incomplete because the SAME call also
copies336 AccountInfo bytes. The complete reached bound337 is used throughout
the per-index matrix. No solver-time/memory-cap increase was made. Fixtures'
unobserved empty data/owner choices are not promoted into production admission;
that full caller-state/domain association remains member B.
