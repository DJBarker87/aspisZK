# SbfLinux criteria and design (before implementation)

Entry: 9f48e742a9df7e628e54aaed4cafead19c4e2537; branch codex/cx-sbf-linux-20261025.
Scope: only tools/sbf-linux-20261025 and evidence/sbf-linux-20261025.
No actual Linux operations, native backend loads, host access, compiler, probe,
wallet, RPC, Rust or Lean execution is authorized. Local pure/mock Python only.

Deliver concrete unexecuted x86_64 Linux 6.8 ABI bindings and fixed guest setup:
namespace unshare then fork (parent remains outside PID namespace), recursive
private propagation, descriptor mount APIs, retained NEW mount root descriptor,
finite tmpfs, private proc, descriptor chroot, stdio and close_range, complete
credential/capability drop, fixed postexec probe, pidfd owned cancellation and
actual direct-child wait before bounded output collection. No path mount or
/proc/self/fd magic, arbitrary argv, user namespace, or host exec fallback.
Device strategy: no guest device mount needed; inherited readonly null stdin
only. Root remains NODEV. /dev is an empty sealed directory.

Copy SbfSeal_setup exactly as SbfLinux_capture (immutable Git source above),
reuse Capture/PublicOutput/manifest validation without edits. Historical 32
ordinary cases and 895 package checks are reused, not new validation. New tests
mock C functions and OS effects, and inspect ctypes layouts without loading C.
All privileged CLI entrypoints unconditionally deny. No caller flag, boolean,
manifest edit or approval allowlist may reach native setup. Internal low-level
functions are reviewable implementation, not authority. Runtime manifest approval
remains null; fresh producer continuation is absent and must be independently
assembled and reviewed. No callback substitutes for producer authority.

Future external route: fresh prospective host admission -> independently capped
3G/4G/swap0/Tasks64 scope -> new inside-Q0 count-once collector GO -> bounded
actual collector/sudo/monitor/helper ancestry and pins -> internal backend.
Neither old marker receipts nor admission.project is authority. This job does
not implement or validate that external route.

Acceptance evidence records exact command/status/wall/RSS/swap, revision and
all package/dependency hashes; axioms N/A. Test unsupported platform before
loading C; exact typed ABI/errno/order; new mount fd versus covered directory;
unshare failure before mount; fork ownership and cancellation; mount flags;
FD closure before limits; IDs/groups/caps/NNP; every injected failure prevents
exec. Mock success is not kernel/runtime or deployed-target validation.

Primary references: exact v6.8 UAPI and kernel source bytes listed and hashed in
SbfLinux-references.json. No installs/clones. Sources downloaded via official
kernel.googlesource.com HTTPS. Kernel and man-page semantics are design inputs,
not successful runtime observations. Preserve failures and blockers.
