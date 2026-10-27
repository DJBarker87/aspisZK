# Admission note

At 11:01:04 UTC the source upload was refused by the documented transient
vanished-cgroup scanner case (session-240148.scope). The standing 30-second
retry rule was observed; the retry at 11:01:54 was an aggregate memory hold.
A local shell sequence had continued to the extraction queue after the
first refused upload. Its barrier refused the command and no extraction was
charged (`charon-source-sha-final-soft-opt-resume9-final-01`, no time.log).
The pending local queue was terminated before a further launch. The earlier
host source hash was 86f27bb59f9646a2deb8c50738c0b6709e5c904b11ff17d5dafcb9976c790d6a;
the intended source hash is recorded by the subsequent verified upload.

The replacement proof-work orchestration uses the unchanged source uploader,
requires a successful admission, verifies local/host SHA-256 equality, and
only then invokes the unchanged extraction queue. No host infrastructure,
resource caps, quiet marker, reservation scanner or shared source was repaired.
No Lean or Kani budget was charged by these refusals.
