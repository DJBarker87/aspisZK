# flock(1) substitute for macOS (no util-linux): exclusive flock(2) on the
# lock file, then run the command; same advisory lock as `flock FILE cmd`.
import fcntl, subprocess, sys
fd = open(sys.argv[1], 'a')
fcntl.flock(fd.fileno(), fcntl.LOCK_EX)
sys.exit(subprocess.call(sys.argv[2:]))
