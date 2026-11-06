"""No host deletion authorized or needed; final check records retained state."""
from pathlib import Path
assert (Path(__file__).resolve().parent/'NLB_CLEANUP.json').is_file()
