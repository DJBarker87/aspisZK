# Stage import cache side effect

L002 imported the shared read-only NHR_stage.py using Python's SourceFileLoader.
Python bytecode caching was not disabled in that historical input. The host
NHR workspace contains __pycache__/NHR_stage.cpython-312.pyc (30540 bytes,
mtime1793866892, coinciding with this staging run), so this was an incidental
shared bytecode-cache write. No shared source or compiled Lean object was edited.
The owned stager now sets sys.dont_write_bytecode=True before loading NHR.
The original L002 source/receipt remains archived; no unchanged stage is rerun.
The peer cache file is preserved rather than deleting outside this job's scratch.
Only own __pycache__ directories are removed before commits. This exception must
not be hidden by a blanket claim that no shared filesystem artifact changed.
