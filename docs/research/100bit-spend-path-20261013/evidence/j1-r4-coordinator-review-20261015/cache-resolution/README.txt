Initial absent dependencies were resolved by reusing retained objects.
No dependency compilation or Lean process ran on the build host.
Remote object files were read and copied, with hashes checked before/after.
All target compiles ran locally with the recorded memory monitor.
The remote-extra pins compare available source hashes to this checkout.
Pinning a retained object and its current source separately does not add an
unrecorded historical source-to-object build attestation. The archived
provenance and original evidence retain that distinction.
The AspisFormal overlay links existing local objects to avoid Lean module
prefix-directory shadowing. No existing cache files were modified.
