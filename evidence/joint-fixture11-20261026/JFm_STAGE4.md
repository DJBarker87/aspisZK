# Stage 4: actual incremental alpha arrays

`JFm_HornerAlpha.transport` proves that the source Horner Segment may use a second array when its selected round coordinate is identical. `JFm_PartialAlpha.horner00`–`09` and `value00`–`09` instantiate it on the arrays containing exactly the challenges reached so far, with zero at later coordinates. This is the array state used by the native round loop. Ten exact bounded Array.update facts and the equality of the final array to the inherited full challenge array are checked.

065 and066 pass, standard axioms only; no caller success or arithmetic result is a premise of the concrete evaluation theorems. No existing module edited, no unchanged dependency rebuilt, no actual-top premise removed. Exact resource/source/axiom receipts are retained per attempt.
