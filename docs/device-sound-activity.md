# Last sound detected in Devices

Each updated recording tab measures incoming sound before VAD and publishes only
its most recent sound timestamp in its existing Devices heartbeat. The heartbeat
still overwrites the same session file about every five seconds and expires after
ten seconds without an update. This feature creates no additional Drive files and
stores no audio samples or sound-level history.

Devices shows the timestamp in the viewing computer's local time, with seconds
and elapsed age. A date is included for a previous day. A new recording (including
the automatic restart after Stop and transcribe) resets the value to **No sound
detected yet**. Pause/resume preserves it. Finishing or aborting keeps the last
value until the next recording. Silence or a lost input stream does not advance
the timestamp. Existing recording, transcription and export behavior is unchanged.

The detector uses a fixed RMS threshold of 0.001 (-60 dBFS), evaluated on incoming
frames before the VAD inference queue. Quiet background noise can exceed this
threshold; very faint sound can fall below it. The indication is not a speech
detector, a microphone-health diagnosis, or proof that both wireless transmitters
are working. It does not stop or restart recording automatically.

An optional `inputActivityVersion: 1` and `lastSoundAt` (Unix milliseconds or
`null`) extend the existing session schema. Older tabs, unknown versions and
invalid timestamps show **Sound activity unavailable**. Save any active recording
before refreshing that tab to load the update. Both recording and viewing tabs
need the update to use the feature. The main recording UI is unchanged.
