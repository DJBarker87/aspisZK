#!/usr/bin/env python3
"""flock(1) substitute for macOS: flock.py <lockfile> <cmd...> (BSD flock, exclusive)."""
import fcntl, subprocess, sys
with open(sys.argv[1], "a") as f:
    fcntl.flock(f, fcntl.LOCK_EX)
    sys.exit(subprocess.call(sys.argv[2:]))
