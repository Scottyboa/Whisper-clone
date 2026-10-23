# Manual transcription and VAD-only downloads

Upload File → Transcribe always runs the pinned Silero speech detector locally
before any Soniox request. It uses the same model and thresholds as live
recording. The checkbox for speaker labels is checked when the page opens and
can still be unchecked for a manual job.

For an app-generated FLAC with a valid segment map, the existing importer first
extracts the originally retained audio. A fresh VAD pass then runs on that audio.
Older WAV metadata is also read before the new pass. Each retained interval is
mapped back through the original segments, including pause gaps and the original
timezone. Ordinary files without that metadata do not gain wall-clock timestamps.

PCM/float WAV and native FLAC files are decoded in chunks in a dedicated worker;
FLAC uses the bundled, pinned libFLAC decoder. A short FLAC variant not fully
decoded by the streaming parser can retry through the browser decoder only if
the complete declared sample count is recovered. This retry is limited to about
33 minutes to bound memory use; longer unsupported variants stop before upload.
Other browser-supported audio formats use the browser's decoder and may require more memory for long files.
Speech detection runs faster than playback where the computer allows it, but
multi-hour recordings can take several minutes. The worker is independent of
the live microphone and is terminated when finished or when the page closes.

The output sent to Soniox is a mono, 16 kHz, 16-bit WAV containing retained speech
with the VAD's pre-speech padding and short pauses. VAD can miss very quiet speech
or accept some non-speech, so keep the original file. The app never overwrites it.
No speech means no Soniox request. Decoding/model/worker failures stop the job;
there is no fallback that uploads the full unprocessed file. Manual transcription
does not automatically save a transcript to Drive.

The VAD processing button uses the same preparation on WAV, FLAC and MP3 without
a Soniox key. It downloads a mono 16 kHz, 16-bit `-VAD.wav`, with available clock
metadata reattached for later import. It does not call Soniox, change the
transcript or upload to Drive, and leaves the original selected. Duplicate VAD
clicks and manual transcription are blocked during processing; live recording
and remote commands remain independent. No speech means no download. Closing
the page cancels the worker and prompts while processing is unfinished.

Automatic Stop and transcribe continues to submit the audio already retained
by the live recorder, without the additional manual VAD pass. Its download,
and ordinary Stop, now use that VAD WAV directly with clock metadata instead
of encoding full-timeline FLAC. Old FLAC imports remain supported.

The exact email body `abort recording` invokes the existing Abort action without
an extra local prompt: it discards the active recording, saves no audio, submits
no transcription and does not restart. Existing background jobs and the email
connection continue. Case and whitespace are normalized; sender/recipient,
blank-subject, freshness and duplicate-message checks remain enforced.
