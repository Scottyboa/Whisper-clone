# Audio enhancement

The **Audio enhancement** checkbox beside Speaker labels is on when the page
opens, including before importing a Soniox key. Uncheck it to retain the prior
audio behavior. Silero VAD, its shared thresholds and microphone settings are
unchanged in either case.

After Silero VAD, enhancement applies a non-resonant 70 Hz Butterworth high-pass
filter and one constant gain over the completed audio. The peak target is
-3 dBFS, with amplification capped at a factor of two (about 6 dB). This is the
same filter/level recipe as the console experiment, applied to the full retained
recording instead of an excerpt. There is no additional noise gate, silence
removal, voice isolation or generative audio model. Enhancement cannot recover
speech already removed by VAD and is not guaranteed to improve every transcript.

The setting is captured for each Stop/Stop and transcribe command, manual
Transcribe or VAD processing click, and Secondary rec confirmation. A later
checkbox change does not alter an already queued job. It is disabled during file
processing/transcription and remains available while recording.

Coverage:

- Live Stop downloads the selected enhanced or unenhanced VAD WAV.
- Stop and transcribe shares that same completed WAV with its background STT
  job; enhancement does not delay starting the next capture or subsequent Abort.
- Upload File + Transcribe runs VAD, then the selected enhancement before Soniox.
- Upload File + VAD processing enhances before generating its downloadable WAV.
- All three Secondary rec modes enhance the completed merged WAV once. The two
  transcription modes submit its audio to Soniox; WAV-only downloads it locally.
- Existing OneDrive choices apply to the resulting transcript, not audio.

The normal VAD pipeline emits canonical 16 kHz mono PCM16; this change keeps that
format. The enhancement routine also preserves separate channels and sample rate
when given other PCM16 WAVs. It never changes sample count, duration, filenames,
original clock maps or Secondary rec source ranges. Metadata chunks are retained
byte-for-byte in downloads and removed by the existing provider preparation;
downloaded and submitted audio samples remain identical within the same job.

Long WAVs are processed with bounded 128 KiB reads and continuous filter state.
The first pass measures the filtered peak, and the second writes PCM with the
chosen gain, without allocating a full decoded Float32 AudioBuffer. Regular
yields keep commands responsive. Page close cancels unfinished enhancement.
With the checkbox off, the routine returns the original File without reading or
rewriting it. A processing failure is reported instead of uploading raw audio as
a fallback. Completed audio is enhanced once per job; manually reimporting it
runs the selected VAD/enhancement workflow again.

Validation includes frequency response against an independent FFmpeg filter,
level limits, chunk boundaries, cancellation, clocks/source metadata, both
checkbox states, shared download/STT samples, and recording command concurrency.
