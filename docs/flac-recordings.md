# Full-timeline recording downloads

Stop and Stop and Transcribe download a standard mono, 16 kHz, 16-bit FLAC.
Retained speech is unchanged from the existing VAD-processed WAV. Removed
intervals, leading/trailing gaps and recording pauses play as digital silence.
The original background sounds discarded by VAD cannot be recovered.

The download follows the recording's clock timeline. A transcript turn at
16:33:12 in a recording that began at 16:00:00 is near playback position
00:33:12. Sub-second VAD tail padding can extend the file by up to one capture
frame. A system-clock discontinuity or unavailable timing causes a visible
fallback to the existing shortened WAV rather than losing the captured speech.

Soniox still receives the existing compact WAV. Download preparation runs in a
separate module worker and never gates automatic restart, transcription or the
OneDrive TXT upload. Multiple downloads are prepared in order. Closing the page
while a download is being prepared triggers the existing unfinished-work prompt.
No audio is added to browser storage, history or OneDrive.

## Reimport

An uppercase `WHISPER_CLONE_TIMING` Vorbis-comment field holds versioned JSON:
recording interval, timezone, total and retained sample counts, and ordered
segments mapping compact samples to full-file samples and original clock times.
This is ordinary FLAC metadata that other players can ignore.

On reimport the app validates the map, stream properties, frame numbering, CRCs,
sample counts and every omitted interval. Only verified zero-valued samples may
be removed. The retained PCM becomes a compact WAV for Soniox, with the original
clock map used for speaker labels. No neural VAD pass is repeated. An entirely
silent app recording produces no provider request.

Older timed WAV files retain their existing support. Ordinary FLAC, re-encoded
FLAC, unsupported metadata versions, invalid maps and damaged frames follow the
existing manual-upload path, without app-side silence trimming. Do not assume
that converting an app FLAC with another audio editor preserves fast reimport or
original clock labels. Worker failures abort preparation rather than silently
uploading a full-length file.

## Bounded processing and format

The encoder implements the RFC 9639 streamable subset, using 4096-sample blocks:
CONSTANT subframes for constant samples and VERBATIM subframes for other audio.
This intentionally favors low CPU use and exact PCM preservation over maximum
speech compression. Silence costs small frame/seek-table overhead, not zero
bytes. Mixed speech/silence boundary blocks and metadata can make a FLAC larger
than its shortened WAV, especially for short or very fragmented recordings.

Seek points roughly every ten seconds allow efficient navigation in players
such as VLC. STREAMINFO's zero MD5 denotes an omitted optional checksum; every
frame has its standard CRC-8 header and CRC-16 footer checksums.

Audio payload reads are limited to roughly 1 MiB (timing metadata to 2 MiB), frame buffers to 4096 samples, and
output is assembled in Blob chunks. Neither export nor reimport allocates a
full-duration PCM buffer for inserted silence. The retained speech and encoded
output still consume memory/disk-backed Blob resources. Metadata is limited to
2 MiB and 50,000 retained intervals; recordings must fit FLAC's sample count and
the compact WAV's 32-bit payload limit.

## Verification

Run `node --test tests/*.test.mjs`. The independent decoder test uses FFmpeg when
installed. Set `WHISPER_TEST_CHROME` to a Chromium executable to also exercise
real module workers, FLAC playback, actual download and manual reimport.
