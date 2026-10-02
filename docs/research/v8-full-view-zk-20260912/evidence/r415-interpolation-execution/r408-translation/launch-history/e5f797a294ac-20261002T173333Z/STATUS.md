# R408 output-name precondition failure (preserved history)

This was a launcher precondition failure, not an Aeneas translation attempt. The remote script stopped immediately because `/home/dombarker/project-offloads/aspis-r408-interpolate-three-limb-translation-20261002-a` already existed. It exited before checking the source/binary fingerprints, creating or modifying the directory, or invoking the translator (systemd service runtime 74 ms). The local `output/` directory is a read-only recursive snapshot copied from that already-existing remote directory by the wrapper; its generated files are not attributed to this task. The exact wrapper/launch log and copied bytes are retained here.

Lead directed the actual authorized translation to a fresh R408 suffix `-b` output root. No retry of Aeneas occurred in this failed precondition attempt.
