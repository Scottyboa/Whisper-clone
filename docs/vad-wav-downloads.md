# VAD WAV downloads

Stop and Stop and transcribe now download the speech retained by the live
Silero VAD directly as a mono, 16 kHz, 16-bit WAV. No silence is reinserted and
no FLAC encoding runs on this path. The filename still includes the original
recording interval and retained audio duration. An entirely silent recording
creates no audio download or transcription; Stop and transcribe still starts
a fresh recording. Download failures do not block restart or transcription.

The recorder's existing `wctm` RIFF chunk stays in the downloaded WAV. Original
clock labels therefore survive later import and further VAD trimming. Audio
playback is shortened: a transcript clock label cannot be converted to a WAV
playback position simply by subtracting the recording start time. Ordinary
players can ignore the private metadata and play the retained audio normally.

Upload File → VAD processing accepts WAV, FLAC and MP3 and uses the same local
Silero pipeline as Upload File → Transcribe. It requires no Soniox key and
downloads `original-name-VAD.wav`. If valid clock metadata existed, the new
segment map is attached; files without it remain without original clock times.
The source file is not overwritten or replaced in the app, and the transcript
field is not changed. Nothing is sent to Soniox or OneDrive. No speech means
no download. Errors are shown and allow another attempt.

Speaker labels remain checked by default. The exact, case-insensitive email
body `abort recording` remains supported for self-addressed mail with an empty
subject: it discards an active or paused recording without saving, processing
or restarting. The connection and earlier background jobs remain active.

Older app FLAC files can still be imported, processed and transcribed. The
codec is retained only for compatibility and its regression tests.
