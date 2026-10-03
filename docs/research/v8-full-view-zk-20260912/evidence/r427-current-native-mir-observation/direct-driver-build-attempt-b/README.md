# R427 direct driver attempt B preparation

This bundle is prepared only. It does not edit the remote candidate, stage files remotely, invoke rustc, or launch a service. Root must review and launch separately.

Attempt B reuses the immutable candidate/cache and exact 46 extern plus 2 native input selection. Its worker expects the canonical-selector hook SHA recorded in `attempt-b-plan.json`, writes only to the fresh `observer-bin-b` and `candidate-audit/direct-driver-build-b` paths, and stages under the fresh `/tmp/aspis-r427-direct-driver-20261003-b` root. The systemd unit is `aspisr427-direct-driver-b.service`.

The original clone audit remains unchanged: the worker first asserts its candidate-tree hook is the original 246d… hash, then changes only that expected map value to the authorized 101336… hash for comparison. Every other tracked source entry and all pinned cached artifacts must match.

The worker and launcher derive from the previously reviewed direct-driver worker and root launcher. Their exact changes are limited to the authorized hook pin/tree-map override and fresh attempt paths/unit. No compilation or MIR observation is claimed.
