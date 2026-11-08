# SPEC-C2 correction proposal (not applied to the frozen files)

Demonstrated error: RegistrationGap.steps_differ (49717).
Source pin: W3 41e76d01fdead952101594b8b0f36a7561d180f2; W4
ce2f78097fa7e3cabc7b66fdfb9445c067917831; frozen COMMON at5e397cb3878.

Before, verbatim:
> On the thread path, `step` is literally
> `PV_THR2_SourceStoreInterpreter.step`, from W4 at the input pin, with its
> `PV_THR2_SourceStoreLibrary.interpret`.

Proposed after:
On the thread path, retain the pinned OwnInit OWNER registration, operator
interpretations and bridged allocation action layers. At ordinary native
writer polls selected by SourceStoreNative.select, apply literally
SourceStoreLibrary.interpret through SourceStoreInterpreter.step, preserving
intrinsic interception priority. Away from those polls execute the retained
OwnInitInterpreterBridged.step. Values remain bound to the named runtime value
interpretations, with source adequacy a separate obligation.

Affected: every thread row using COMMON, particularly f361 and OwnInit.
No source, endpoint, trust or metric change. No old provider is edited.
No success/write-definedness premise is added. This records a proposal,
not authorization to rewrite shared frozen files or a completed row contract.
