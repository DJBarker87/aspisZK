# Owned serial queue receipts

Queue manifests are development plans and stop immediately on an unexpected exit or incomplete control. Jobs after a stop are not executed. Attempt IDs are authoritative only when NHU_ATTEMPTS.jsonl contains their completed receipt. Later queues reuse only numbers never submitted; this is not a process resubmission. The runner refuses an existing receipt directory. Controls re-upload the positive attempt's immutable source snapshot and add only the intended corruption cfg. No two scopes run concurrently.
