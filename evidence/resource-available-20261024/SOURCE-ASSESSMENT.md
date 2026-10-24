# ResourceAvailable primary source assessment

Read complete immutable HEAD ResourceHierarchy candidate/GO, membership,
accounting and binding, objects/replay/audit/tests, source assessment and summary.
ResourceHierarchy e6c57652a7 reviewed result is reused, never a new host gate.
Existing ResourceStat assessment and ResourceHierarchy cgroup source pointers
are REUSED; their non-atomicity and type/LRU overlap limitations remain.
No separate ResourceKernel package is present in entry HEAD; no host reread
is substituted for that absence.

Primary web fetch failures retained: upstream v6.8 mm/show_mem.c timed out;
Launchpad exact-tag show_mem.c and meminfo.c URLs were inaccessible through
web tool. No unchanged fetch retry was made. A distinct direct HTTPS curl
transport, --retry 0 --max-time 30, succeeded for both exact Ubuntu files:
https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/plain/mm/show_mem.c?h=Ubuntu-6.8.0-147.147
SHA256 29c0c6f784bf30c666e0f8416e0e4c36ca65bdcbbd4ecccc0218b40bf24aee18 size 12086.
https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/plain/fs/proc/meminfo.c?h=Ubuntu-6.8.0-147.147
SHA256 2c6f41b68527711de9d417d62dd5a7c9b22ff4fb04c7e649a28ee51f0be8fcae size 5890.
Upstream v6.8 meminfo.c web read also confirms K=S+misc (lines 100-103).
No GPL source copied into Git. Exact formula and reserve derivation are in
CRITERIA.md. No kernel binary identity established or needed for the offline
reference argument. No security-contract/native-proof or cryptographic claim.
Final Kani remains 59/60; target not yet established.

The primary formula uses page units; CRITERIA.md explicitly converts kernel
half-page counters before comparing byte quantities. This clarification changes
no predicate, constants, tests, or passing results. Full B remains charged.
New observer causal replay reproduces 6,908 ordered reads in each snapshot,
including expected root ENOENT and threaded EOPNOTSUPP, matching complete raw
inputs, receipt text, uint fields, identities and hashes. The original ordered
15,015-event replay also covers legacy ps/systemctl/Docker and proc-self reads.
The older 14,587-event audit/source assessments are reused without rerunning
those gates. Their new-metric counterfactuals are all DENY. This demonstrates
that the proposal does not preserve old estimates or imply blanket admission.
