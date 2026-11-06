# NJD failures and findings

Seed verifier initially included NIV_EXPORT.json in the object byte count. All twelve objects match the required export; the additional 2412 bytes are its self manifest. Own checker now separates objects and metadata without relaxing any object hash check; no proof launched before this repair.

K001: guard source compiled and CBMC ran; inherited data_len contract precondition failed on independently selected length Err(AccountBorrowFailed) and bytes Err(InvalidAccountData). Corrected constructor pairs borrow failures, preserving the exact snapshot_domain. Not a timeout; no credit. Earlier L001/L002 failed only incorrect diagnostic names. L001 receipt collection lacked the owned INPUTS directory; recovered read-only without resubmission and repaired the own collector.
