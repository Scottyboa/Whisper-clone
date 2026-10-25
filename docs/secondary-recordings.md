# Secondary recordings

Use Secondary rec after importing a Soniox key. Select up to 1,000 WAVs named
like `R-00058_2610251719_SVOS.WAV` or `R-00059_2610252019_REC.WAV`, then
choose an output mode and confirm. Both endings can be mixed in the
same selection, and filename matching is case-insensitive.

The name encodes YY MM DD HH mm. Dates and times are used exactly as written
in those filenames, without timezone or daylight-saving adjustments. For
example, `2610252019_REC` means 25 October 2026 at 20:19. Calendar dates, hour
and minute are validated; unknown names and duplicate filenames fail before
processing. Files sort by filename date and time, then recorder sequence number
for tied minutes. File modification timestamps are never used. Filename years
are interpreted as 2000–2099.

The options prompt offers two mutually exclusive checkboxes:

- VAD Silero + transcribe: merge and transcribe without a WAV download.
- VAD Silero + WAV download + transcribe: the same processing plus a merged WAV
  download. This option is checked each time the prompt opens.

Selecting one clears the other, and the audio is processed/transcribed once.
With neither selected, the action button becomes Exit. Cancel, the red close
button and Escape also dismiss the prompt without processing. Both modes keep
speaker labels, filename-based dates, original-file sections, metadata and the
same transcript title/export name. The merged audio stays selected in memory
for a manual retry in either mode; there is no automatic Drive upload.

Each source receives the same pinned Silero VAD as manual transcription. One
worker/model is reused for the batch, with its frame and model state reset
between files. Standard WAV formats are decoded in bounded chunks and converted
to mono 16 kHz, 16-bit retained PCM. Other browser-supported WAV encodings use
the existing native decoder fallback. Processing is sequential, and Blob slices
are combined without copying all retained PCM into another full-length array.
A decoding/VAD failure stops the batch before any partial provider request.
The worker is released on success, error or page close.

The downloaded WAV starts with `secondary rec - ` and uses the usual recording
filename format. The interval uses the filename dates and times of the first and last selected files;
the last filename time is the last clip's start label, not a measured stop time.
Seconds are 00 placeholders because these names contain only minute precision.
The parenthesized duration is the merged retained audio duration, rounded with
the app's existing duration formatter. Both dates appear when crossing midnight.
Silence between clips is not reinserted. Original files are not modified.

The app submits that merged speech to Soniox once, with speaker diarization on
and no redundant VAD pass. Transcript tokens are assigned to their original
source sections by their sample offsets in the merged audio. Speaker paragraphs
restart at every source boundary, even if the speaker label is unchanged.
Sections show the filename date and minute, alongside the unchanged
original filename for reference. The merge confirmation, WAV name, TXT title,
section headings and Drive export name all use those original labels. A source
with no detected speech gets an explicit marker; an entirely silent batch produces no WAV or
provider job. If Soniox returns text without usable timestamps, grouping fails
visibly rather than assigning text to an invented source section.

The transcript's first line is its title in the existing full-interval/VAD TXT
format, prefixed `secondary rec - `. EX.Drive keeps that filename when saving to
the chosen folders. This manual workflow does not automatically upload to Drive.
Normal transcription and Drive import reset the special export filename.
Audio download failures are reported independently and do not prevent Soniox
processing. The merged file remains selected for retry if the provider fails.
Recording and its existing email/Devices commands continue independently.

## Source metadata and reimport

A private `wcsr` RIFF chunk stores a versioned map with source names, dates and
minutes, plus sample ranges identifying which source each retained part belongs
to. Version 3 stores the original filename labels. Version 1 WAVs already used
raw labels and remain supported. Version 2 WAVs from the temporary clock patch
are validated using their old metadata rules, then restored to the original
filename labels on import. No hour adjustment is applied to current input or
output. Reimport and additional VAD passes preserve the version 3 labels.
Imported secondary audio receives its generated filename based on those labels
for further processing/downloads. Players can ignore the private chunk.
Reimport validates the metadata and strips it before provider upload. A later
manual VAD pass composes new cuts through the source sample ranges.

It does not invent wall-clock timestamps inside voice-activated clips, which
may already have discarded intervals. Legacy app WAV/FLAC clock maps continue
to use their existing separate metadata support. Re-encoding with another tool
may remove private metadata.

Metadata is bounded to 2 MiB and 50,000 ranges; merged audio must fit the normal
RIFF/WAV 32-bit size limit. Large batches still need memory for retained audio
and temporary Blobs. Closing/reloading interrupts unfinished work and uses the
existing unfinished-work prompt. No source files or audio archives are stored
in localStorage, sessionStorage, IndexedDB or OneDrive by this feature.

## Validation

Run `node --test tests/*.test.mjs`. Set WHISPER_TEST_CHROME to Chromium to include
the real worker/model browser checks. They use synthetic speech and a mocked
Soniox service, validating a single upload, real WAV playback, the silent source
section, the filename interval, model reuse and metadata after a fresh VAD pass.
