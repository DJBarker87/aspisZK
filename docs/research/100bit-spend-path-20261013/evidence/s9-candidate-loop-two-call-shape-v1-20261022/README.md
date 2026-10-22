# Actual candidate loop shape

PROVED: `helper_success_two_body_calls` derives two exact active body results, their iterator transitions, the same intermediate array, the actual final array and the terminal body result from one successful generated-candidate loop execution. The proof uses the existing actual candidate success-evidence producer and inverts the same suffix; it does not substitute the selected P6 model.

RETAINED: the theorem begins with success of the candidate helper loop at the initial range. It describes control flow and shared values; it does not prove the arithmetic specification or candidate-to-P6 correspondence.

Validation: focused Lean 4.32 compilation, -j1 -M4400, atomic local mutex, aggregate RSS watchdog; standard axioms only. Exact status, revision, wall time, peak RSS and observed swaps are retained. Imported warm object hashes are pinned; no compiled objects included and no coherent release replay claimed.

OPEN: suffix transport, candidate helper correspondence, frozen source/library/caller and artifact joins, and the composed 100-bit theorem. Production source is unchanged. Run `python3 -B check_packet.py` for evidence checks without compilation.
