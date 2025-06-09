// recording.js
// Updated recording module without encryption/HMAC mechanisms,
// processing audio chunks using OfflineAudioContext,
// and implementing a client-side transcription queue that sends each processed chunk directly to Speechmatics (enhanced Norwegian).

function hashString(str) {
  let hash = 0;
  for (let i = 0; i < str.length; i++) {
    const char = str.charCodeAt(i);
    hash = ((hash << 5) - hash) + char;
    hash |= 0; // Convert to 32-bit signed integer
  }
  // Convert to an unsigned 32-bit integer and return as string.
  return (hash >>> 0).toString();
}

const DEBUG = true;
function logDebug(message, ...optionalParams) {
  if (DEBUG) {
    console.debug(new Date().toISOString(), "[DEBUG]", message, ...optionalParams);
  }
}
function logInfo(message, ...optionalParams) {
  console.info(new Date().toISOString(), "[INFO]", message, ...optionalParams);
}
function logError(message, ...optionalParams) {
  console.error(new Date().toISOString(), "[ERROR]", message, ...optionalParams);
}

const MIN_CHUNK_DURATION = 120000; // 120 seconds
const MAX_CHUNK_DURATION = 120000; // 120 seconds
const watchdogThreshold = 1500;   // 1.5 seconds with no frame

let mediaStream = null;
let processedAnyAudioFrames = false;
let audioReader = null;
let recordingStartTime = 0;
// Accumulate time from all active segments
let accumulatedRecordingTime = 0;
let recordingTimerInterval;
let completionTimerInterval = null;
let completionStartTime = 0;
let groupId = null;
let chunkNumber = 1;
let manualStop = false;
let transcriptChunks = {};  // {chunkNumber: transcript}
let pollingIntervals = {};  // (removed polling functions, kept for legacy structure)

let chunkStartTime = 0;
let lastFrameTime = 0;
let chunkTimeoutId;

let chunkProcessingLock = false;
let pendingStop = false;
let finalChunkProcessed = false;
let recordingPaused = false;
let audioFrames = []; // Buffer for audio frames

// --- New Transcription Queue Variables ---
let transcriptionQueue = [];  // Queue of { chunkNumber, wavBlob }
let isProcessingQueue = false;

// --- Utility Functions ---
function updateStatusMessage(message, color = "#333") {
  const statusElem = document.getElementById("statusMessage");
  if (statusElem) {
    statusElem.innerText = message;
    statusElem.style.color = color;
  }
}

function formatTime(ms) {
  const totalSec = Math.floor(ms / 1000);
  if (totalSec < 60) {
    return totalSec + " sec";
  } else {
    const minutes = Math.floor(totalSec / 60);
    const seconds = totalSec % 60;
    return minutes + " min" + (seconds > 0 ? " " + seconds + " sec" : "");
  }
}

function updateRecordingTimer() {
  // Timer shows accumulated time plus current active segment time
  const elapsed = accumulatedRecordingTime + (Date.now() - recordingStartTime);
  const timerElem = document.getElementById("recordTimer");
  if (timerElem) {
    timerElem.innerText = "Recording Timer: " + formatTime(elapsed);
  }
}

function stopMicrophone() {
  if (mediaStream) {
    mediaStream.getTracks().forEach(track => track.stop());
    mediaStream = null;
    logInfo("Microphone stopped.");
  }
  if (audioReader) {
    audioReader.cancel();
    audioReader = null;
  }
}

// --- Base64 Helper Functions (kept for legacy) ---
function arrayBufferToBase64(buffer) {
  let binary = "";
  const bytes = new Uint8Array(buffer);
  for (let i = 0; i < bytes.byteLength; i++) {
    binary += String.fromCharCode(bytes[i]);
  }
  return window.btoa(binary);
}
function base64ToArrayBuffer(base64) {
  const binary = window.atob(base64);
  const len = binary.length;
  const bytes = new Uint8Array(len);
  for (let i = 0; i < len; i++) {
    bytes[i] = binary.charCodeAt(i);
  }
  return bytes;
}

// --- Device Token Management ---
function getDeviceToken() {
  let token = localStorage.getItem("device_token");
  if (!token) {
    token = crypto.randomUUID();
    localStorage.setItem("device_token", token);
  }
  return token;
}

// --- API Key Retrieval ---
// With encryption removed, we now simply get the API key from sessionStorage.
function getAPIKey() {
  return sessionStorage.getItem("user_api_key");
}

// --- File Blob Processing ---
// Previously used for encryption; now simply returns the original blob along with markers.
async function encryptFileBlob(blob) {
  const apiKey = getAPIKey();
  if (!apiKey) throw new Error("API key not available");
  const deviceToken = getDeviceToken();
  const apiKeyMarker = hashString(apiKey);
  const deviceMarker = hashString(deviceToken);
  // Return the original blob without any encryption; iv and salt are empty.
  return {
    encryptedBlob: blob,
    iv: "",
    salt: "",
    apiKeyMarker,
    deviceMarker
  };
}

// --- OfflineAudioContext Processing ---
// This function takes interleaved PCM samples (Float32Array), the original sample rate, and the number of channels,
// converts the audio to mono (averaging channels if needed), resamples to 16kHz, and applies 0.3s fade-in/out.
// It returns a 16-bit PCM WAV Blob.
async function processAudioUsingOfflineContext(pcmFloat32, originalSampleRate, numChannels) {
  const targetSampleRate = 16000;
  
  // Calculate the number of frames
  const numFrames = pcmFloat32.length / numChannels;
  
  // Create an AudioBuffer in a temporary AudioContext
  let tempCtx = new AudioContext();
  let originalBuffer = tempCtx.createBuffer(numChannels, numFrames, originalSampleRate);
  
  if (numChannels === 1) {
    originalBuffer.copyToChannel(pcmFloat32, 0);
  } else {
    // Deinterleave and copy each channel
    for (let ch = 0; ch < numChannels; ch++) {
      let channelData = new Float32Array(numFrames);
      for (let i = 0; i < numFrames; i++) {
        channelData[i] = pcmFloat32[i * numChannels + ch];
      }
      originalBuffer.copyToChannel(channelData, ch);
    }
  }
  // Convert to mono by averaging channels if necessary
  let monoBuffer;
  if (numChannels > 1) {
    let monoData = new Float32Array(numFrames);
    for (let i = 0; i < numFrames; i++) {
      let sum = 0;
      for (let ch = 0; ch < numChannels; ch++) {
        sum += originalBuffer.getChannelData(ch)[i];
      }
      monoData[i] = sum / numChannels;
    }
    monoBuffer = tempCtx.createBuffer(1, numFrames, originalSampleRate);
    monoBuffer.copyToChannel(monoData, 0);
  } else {
    monoBuffer = originalBuffer;
  }
  tempCtx.close();
  
  // Set up OfflineAudioContext for resampling
  const duration = monoBuffer.duration;
  const offlineCtx = new OfflineAudioContext(1, targetSampleRate * duration, targetSampleRate);
  
  const source = offlineCtx.createBufferSource();
  source.buffer = monoBuffer;
  
  const gainNode = offlineCtx.createGain();
  const fadeDuration = 0.3;
  gainNode.gain.setValueAtTime(0, 0);
  gainNode.gain.linearRampToValueAtTime(1, fadeDuration);

  const fadeOutStart = Math.max(0, duration - fadeDuration);
  if (duration < fadeDuration * 2) {
    console.warn(`[Audio] Short chunk (${duration.toFixed(2)}s) — fade-in/out may be squished`);
  }
  gainNode.gain.setValueAtTime(1, fadeOutStart);
  gainNode.gain.linearRampToValueAtTime(0, duration);
  
  source.connect(gainNode).connect(offlineCtx.destination);
  source.start(0);
  
  const renderedBuffer = await offlineCtx.startRendering();
  const processedData = renderedBuffer.getChannelData(0);
  const processedInt16 = floatTo16BitPCM(processedData);
  const wavBlob = encodeWAV(processedInt16, targetSampleRate, 1);
  return wavBlob;
}

// --- New: Transcribe Chunk via Speechmatics ---
// Sends each WAV blob to Speechmatics, polls until complete, then returns the transcript.
async function transcribeChunkViaSpeechmatics(wavBlob, chunkNum) {
  logDebug(`transcribeChunkViaSpeechmatics: chunk ${chunkNum} entry`);
  const totalStart = Date.now();
  const smKey = getAPIKey();
  if (!smKey) {
    logError(`No API key for Speechmatics when processing chunk ${chunkNum}`);
    throw new Error("API key not available for Speechmatics");
  }

  // 1) Create the job
  const form = new FormData();
  const config = {
    type: "transcription",
    transcription_config: {
      language: "no",           
      operating_point: "enhanced"
    }
  };
  form.append("config", JSON.stringify(config));
  form.append("data_file", wavBlob, `chunk_${chunkNum}.wav`);

  logDebug(`transcribeChunkViaSpeechmatics: creating job for chunk ${chunkNum}`);
  const createStart = Date.now();
  const createResp = await fetch("https://asr.api.speechmatics.com/v2/jobs/", {
    method: "POST",
    headers: { "Authorization": "Bearer " + smKey },
    body: form
  });
  const createEnd = Date.now();
  logDebug(`job creation request duration ${createEnd - createStart} ms`);

  if (!createResp.ok) {
    const errText = await createResp.text();
    logError(`Speechmatics create job failed [${createResp.status}]: ${errText}`);
    throw new Error(`Speechmatics job creation failed: ${errText}`);
  }
  const createJson = await createResp.json();
  const job        = createJson.job || createJson;
  let status       = job.status;

  // 2) Poll until done
  logDebug(`transcribeChunkViaSpeechmatics: polling job ${job.id} for chunk ${chunkNum}`);
  const pollStart = Date.now();
  let pollCount = 0;
  while (status !== "done") {
    await new Promise(r => setTimeout(r, 1000));
    pollCount++;
    const statusResp = await fetch(
      `https://asr.api.speechmatics.com/v2/jobs/${job.id}/`,
      { headers: { "Authorization": "Bearer " + smKey } }
    );
    const statusJson = await statusResp.json();
    const detail = statusJson.job
                  || (Array.isArray(statusJson.jobs) && statusJson.jobs[0])
                  || statusJson;
    status = detail.status;
  }
  const pollEnd = Date.now();
  logDebug(`polling done for job ${job.id}, attempts=${pollCount}, duration ${pollEnd - pollStart} ms`);

  if (status !== "done") {
    throw new Error(`Speechmatics job ${job.id} failed with status ${status}`);
  }

  // 3) Download transcript
  logDebug(`transcribeChunkViaSpeechmatics: downloading transcript for job ${job.id}`);
  const downloadStart = Date.now();
  const txtResp = await fetch(
    `https://asr.api.speechmatics.com/v2/jobs/${job.id}/transcript?format=txt`,
    { headers: { "Authorization": "Bearer " + smKey } }
  );
  const downloadEnd = Date.now();
  logDebug(`download duration ${downloadEnd - downloadStart} ms`);

  if (!txtResp.ok) {
    const errText = await txtResp.text();
    logError(`Transcript download failed [${txtResp.status}]: ${errText}`);
    throw new Error(`Failed fetching transcript: ${errText}`);
  }
  const text = await txtResp.text();
  const totalEnd = Date.now();
  logDebug(`transcribeChunkViaSpeechmatics: chunk ${chunkNum} total duration ${totalEnd - totalStart} ms`);
  return text;
}

// --- Transcription Queue Processing ---
async function processTranscriptionQueue() {
  logDebug("processTranscriptionQueue: entry", { queueLength: transcriptionQueue.length });
  if (isProcessingQueue) {
    logDebug("processTranscriptionQueue: already running, exiting");
    return;
  }
  isProcessingQueue = true;

  while (transcriptionQueue.length > 0) {
    const { chunkNum, wavBlob } = transcriptionQueue.shift();
    logInfo(`Starting transcription chunk ${chunkNum}, remaining in queue: ${transcriptionQueue.length}`);
    try {
      const transcript = await transcribeChunkViaSpeechmatics(wavBlob, chunkNum);
      transcriptChunks[chunkNum] = transcript;
      updateTranscriptionOutput();
      logInfo(`Completed transcription chunk ${chunkNum}`);
    } catch (err) {
      logError(`Failed transcription chunk ${chunkNum}:`, err);
      transcriptChunks[chunkNum] = `[Error on chunk ${chunkNum}]`;
      updateTranscriptionOutput();
    }
  }

  isProcessingQueue = false;
  logDebug("processTranscriptionQueue: exit");
}

// Adds a processed chunk to the queue and processes chunks sequentially.
function enqueueTranscription(wavBlob, chunkNum) {
  transcriptionQueue.push({ chunkNum, wavBlob });
  processTranscriptionQueue();
}

// --- Removed: Polling functions (pollChunkTranscript) since we now transcribe directly ---

// --- Audio Chunk Processing ---
async function processAudioChunkInternal(force = false) {
  if (audioFrames.length === 0) {
    logDebug("No audio frames to process.");
    return;
  }
  processedAnyAudioFrames = true;

  logInfo(`Processing ${audioFrames.length} audio frames for chunk ${chunkNumber}.`);
  logDebug(`processAudioChunkInternal: start chunk ${chunkNumber}`);
  const internalStart = Date.now();

  const framesToProcess = audioFrames;
  audioFrames = []; // Clear the buffer
  const sampleRate = framesToProcess[0].sampleRate;
  const numChannels = framesToProcess[0].numberOfChannels;
  let pcmDataArray = [];

  for (const frame of framesToProcess) {
    const numFrames = frame.numberOfFrames;
    if (numChannels === 1) {
      const channelData = new Float32Array(numFrames);
      frame.copyTo(channelData, { planeIndex: 0 });
      pcmDataArray.push(channelData);
    } else {
      let channelData = [];
      for (let c = 0; c < numChannels; c++) {
        const channelArray = new Float32Array(numFrames);
        frame.copyTo(channelArray, { planeIndex: c });
        channelData.push(channelArray);
      }
      const interleaved = new Float32Array(numFrames * numChannels);
      for (let i = 0; i < numFrames; i++) {
        for (let c = 0; c < numChannels; c++) {
          interleaved[i * numChannels + c] = channelData[c][i];
        }
      }
      pcmDataArray.push(interleaved);
    }
    frame.close();
  }

  const totalLength = pcmDataArray.reduce((sum, arr) => sum + arr.length, 0);
  const pcmFloat32 = new Float32Array(totalLength);
  let offset = 0;
  for (const arr of pcmDataArray) {
    pcmFloat32.set(arr, offset);
    offset += arr.length;
  }

  logDebug(`processAudioChunkInternal: calling OfflineAudioContext for chunk ${chunkNumber}`);
  const procStart = Date.now();
  const wavBlob = await processAudioUsingOfflineContext(pcmFloat32, sampleRate, numChannels);
  const procEnd = Date.now();
  logDebug(`processAudioUsingOfflineContext: chunk ${chunkNumber} duration ${procEnd - procStart} ms`);

  const enqueueStart = Date.now();
  enqueueTranscription(wavBlob, chunkNumber);
  const enqueueEnd = Date.now();
  logDebug(`enqueueTranscription: chunk ${chunkNumber} queue add duration ${enqueueEnd - enqueueStart} ms`);

  const internalEnd = Date.now();
  logDebug(`processAudioChunkInternal: end chunk ${chunkNumber}, total duration ${internalEnd - internalStart} ms`);
  chunkNumber++;
}

async function safeProcessAudioChunk(force = false) {
  if (manualStop && finalChunkProcessed) {
    logDebug("Final chunk already processed; skipping safeProcessAudioChunk.");
    return;
  }
  if (chunkProcessingLock) {
    logDebug("Chunk processing is locked; skipping safeProcessAudioChunk.");
    return;
  }
  chunkProcessingLock = true;
  await processAudioChunkInternal(force);
  chunkProcessingLock = false;
  if (pendingStop) {
    pendingStop = false;
    finalizeStop();
  }
}

function finalizeStop() {
  completionStartTime = Date.now();
  completionTimerInterval = setInterval(() => {
    const timerElem = document.getElementById("transcribeTimer");
    if (timerElem) {
      timerElem.innerText = "Completion Timer: " + formatTime(Date.now() - completionStartTime);
    }
  }, 1000);
  const startButton = document.getElementById("startButton");
  const stopButton = document.getElementById("stopButton");
  const pauseResumeButton = document.getElementById("pauseResumeButton");
  if (startButton) startButton.disabled = false;
  if (stopButton) stopButton.disabled = true;
  if (pauseResumeButton) pauseResumeButton.disabled = true;
  logInfo("Recording stopped by user. Finalizing transcription.");
}

function updateTranscriptionOutput() {
  const sortedKeys = Object.keys(transcriptChunks).map(Number).sort((a, b) => a - b);
  let combinedTranscript = "";
  sortedKeys.forEach(key => {
    combinedTranscript += transcriptChunks[key] + " ";
  });
  const transcriptionElem = document.getElementById("transcription");
  if (transcriptionElem) {
    transcriptionElem.value = combinedTranscript.trim();
  }
  if (manualStop && Object.keys(transcriptChunks).length >= (chunkNumber - 1)) {
    clearInterval(completionTimerInterval);
    updateStatusMessage("Transcription finished!", "green");
    logInfo("Transcription complete.");
  }
}

function floatTo16BitPCM(input) {
  const output = new Int16Array(input.length);
  for (let i = 0; i < input.length; i++) {
    let s = Math.max(-1, Math.min(1, input[i]));
    output[i] = s < 0 ? s * 0x8000 : s * 0x7FFF;
  }
  return output;
}

function encodeWAV(samples, sampleRate, numChannels) {
  const buffer = new ArrayBuffer(44 + samples.length * 2);
  const view = new DataView(buffer);
  function writeString(offset, string) {
    for (let i = 0; i < string.length; i++) {
      view.setUint8(offset + i, string.charCodeAt(i));
    }
  }
  writeString(0, 'RIFF');
  view.setUint32(4, 36 + samples.length * 2, true);
  writeString(8, 'WAVE');
  writeString(12, 'fmt ');
  view.setUint32(16, 16, true);
  view.setUint16(20, 1, true);
  view.setUint16(22, numChannels, true);
  view.setUint32(24, sampleRate, true);
  view.setUint32(28, sampleRate * numChannels * 2, true);
  view.setUint16(32, numChannels * 2, true);
  view.setUint16(34, 16, true);
  writeString(36, 'data');
  view.setUint32(40, samples.length * 2, true);
  let offset = 44;
  for (let i = 0; i < samples.length; i++, offset += 2) {
    view.setInt16(offset, samples[i], true);
  }
  return new Blob([view], { type: 'audio/wav' });
}

function scheduleChunk() {
  logDebug("scheduleChunk: checking conditions", {
    manualStop,
    recordingPaused,
    elapsed: Date.now() - chunkStartTime,
    timeSinceLast: Date.now() - lastFrameTime
  });
  if (manualStop || recordingPaused) {
    logInfo("scheduleChunk: suspended (stop or pause)");
    return;
  }
  const elapsed = Date.now() - chunkStartTime;
  const timeSinceLast = Date.now() - lastFrameTime;
  if (
    elapsed >= MAX_CHUNK_DURATION ||
    (elapsed >= MIN_CHUNK_DURATION && timeSinceLast >= watchdogThreshold)
  ) {
    logInfo(`scheduleChunk: condition met (elapsed=${elapsed} ms, sinceLast=${timeSinceLast} ms); processing chunk ${chunkNumber}`);
    safeProcessAudioChunk();
    chunkStartTime = Date.now();
    scheduleChunk();
  } else {
    chunkTimeoutId = setTimeout(scheduleChunk, 500);
    logDebug("scheduleChunk: next check in 500ms");
  }
}

function resetRecordingState() {
  Object.values(pollingIntervals).forEach(interval => clearInterval(interval));
  pollingIntervals = {};
  clearTimeout(chunkTimeoutId);
  clearInterval(recordingTimerInterval);
  transcriptChunks = {};
  audioFrames = [];
  chunkStartTime = Date.now();
  lastFrameTime = Date.now();
  manualStop = false;
  finalChunkProcessed = false;
  recordingPaused = false;
  groupId = Date.now().toString();
  chunkNumber = 1;
  accumulatedRecordingTime = 0;
}

function initRecording() {
  const startButton = document.getElementById("startButton");
  const stopButton = document.getElementById("stopButton");
  const pauseResumeButton = document.getElementById("pauseResumeButton");
  if (!startButton || !stopButton || !pauseResumeButton) return;

  startButton.addEventListener("click", async () => {
    const dgKey = getAPIKey();
    if (!dgKey) {
      alert("Please enter a valid API key before starting the recording.");
      return;
    }
    resetRecordingState();

    const transcriptionElem = document.getElementById("transcription");
    if (transcriptionElem) transcriptionElem.value = "";

    updateStatusMessage("Recording...", "green");
    logInfo("Recording started.");
    try {
      mediaStream = await navigator.mediaDevices.getUserMedia({ audio: true });
      if (recordingTimerInterval) {
        clearInterval(recordingTimerInterval);
        recordingTimerInterval = null;
      }

      recordingStartTime = Date.now();
      recordingTimerInterval = setInterval(updateRecordingTimer, 1000);

      const track = mediaStream.getAudioTracks()[0];
      const processor = new MediaStreamTrackProcessor({ track: track });
      audioReader = processor.readable.getReader();

      function readLoop() {
        audioReader.read().then(({ done, value }) => {
          if (done) {
            logInfo("Audio track reading complete.");
            return;
          }
          lastFrameTime = Date.now();
          audioFrames.push(value);
          readLoop();
        }).catch(err => {
          logError("Error reading audio frames", err);
        });
      }
      readLoop();
      scheduleChunk();
      logInfo("MediaStreamTrackProcessor started, reading audio frames.");
      startButton.disabled = true;
      stopButton.disabled = false;
      pauseResumeButton.disabled = false;
      pauseResumeButton.innerText = "Pause Recording";
    } catch (error) {
      updateStatusMessage("Microphone access error: " + error, "red");
      logError("Microphone access error", error);
    }
  });

  pauseResumeButton.addEventListener("click", async () => {
    if (!mediaStream || recordingPaused) {
      try {
        mediaStream = await navigator.mediaDevices.getUserMedia({ audio: true });
        const newTrack = mediaStream.getAudioTracks()[0];
        const processor = new MediaStreamTrackProcessor({ track: newTrack });
        audioReader = processor.readable.getReader();

        function readLoop() {
          audioReader.read().then(({ done, value }) => {
            if (done) {
              logInfo("Audio track reading complete.");
              return;
            }
            lastFrameTime = Date.now();
            audioFrames.push(value);
            readLoop();
          }).catch(err => {
            logError("Error reading audio frames", err);
          });
        }
        readLoop();

        recordingPaused = false;
        if (recordingTimerInterval) {
          clearInterval(recordingTimerInterval);
          recordingTimerInterval = null;
        }

        recordingStartTime = Date.now();
        lastFrameTime = Date.now();
        recordingTimerInterval = setInterval(updateRecordingTimer, 1000);

        pauseResumeButton.innerText = "Pause Recording";
        updateStatusMessage("Recording...", "green");
        chunkStartTime = Date.now();
        scheduleChunk();
        logInfo("Recording resumed.");
      } catch (error) {
        updateStatusMessage("Error resuming recording: " + error, "red");
        logError("Error resuming microphone on resume", error);
      }
    } else {
      await safeProcessAudioChunk(false);
      accumulatedRecordingTime += Date.now() - recordingStartTime;
      stopMicrophone();
      recordingPaused = true;
      clearInterval(recordingTimerInterval);
      clearTimeout(chunkTimeoutId);
      pauseResumeButton.innerText = "Resume Recording";
      updateStatusMessage("Recording paused", "orange");
      logInfo("Recording paused; current chunk processed and media stream stopped.");
      const startButton = document.getElementById("startButton");
      const stopButton = document.getElementById("stopButton");
      if (startButton) startButton.disabled = true;
      if (stopButton) stopButton.disabled = false;
      pauseResumeButton.disabled = false;
    }
  });

  stopButton.addEventListener("click", async () => {
    updateStatusMessage("Finishing transcription...", "blue");
    manualStop = true;
    clearTimeout(chunkTimeoutId);
    clearInterval(recordingTimerInterval);
    stopMicrophone();
    chunkStartTime = 0;
    lastFrameTime = 0;
    await new Promise(resolve => setTimeout(resolve, 200));

    if (recordingPaused) {
      finalChunkProcessed = true;
      const compTimerElem = document.getElementById("transcribeTimer");
      if (compTimerElem) {
        compTimerElem.innerText = "Completion Timer: 0 sec";
      }
      updateStatusMessage("Transcription finished!", "green");
      const startButton = document.getElementById("startButton");
      if (startButton) startButton.disabled = false;
      stopButton.disabled = true;
      const pauseResumeButton = document.getElementById("pauseResumeButton");
      if (pauseResumeButton) pauseResumeButton.disabled = true;
      logInfo("Recording paused and stop pressed; transcription complete without extra processing.");
      return;
    }

    if (audioFrames.length === 0 && !processedAnyAudioFrames) {
      resetRecordingState();
      if (completionTimerInterval) clearInterval(completionTimerInterval);
      const compTimerElem = document.getElementById("transcribeTimer");
      if (compTimerElem) compTimerElem.innerText = "Completion Timer: 0 sec";
      const recTimerElem = document.getElementById("recordTimer");
      if (recTimerElem) recTimerElem.innerText = "Recording Timer: 0 sec";
      updateStatusMessage("Recording reset. Ready to start.", "green");
      const startButton = document.getElementById("startButton");
      if (startButton) startButton.disabled = false;
      stopButton.disabled = true;
      const pauseResumeButton = document.getElementById("pauseResumeButton");
      if (pauseResumeButton) pauseResumeButton.disabled = true;
      processedAnyAudioFrames = false;
      return;
    } else {
      if (chunkProcessingLock) {
        pendingStop = true;
        logDebug("Chunk processing locked at stop; setting pendingStop.");
      } else {
        await safeProcessAudioChunk(true);
        if (!processedAnyAudioFrames) {
          resetRecordingState();
          if (completionTimerInterval) clearInterval(completionTimerInterval);
          const compTimerElem = document.getElementById("transcribeTimer");
          if (compTimerElem) compTimerElem.innerText = "Completion Timer: 0 sec";
          const recTimerElem = document.getElementById("recordTimer");
          if (recTimerElem) recTimerElem.innerText = "Recording Timer: 0 sec";
          updateStatusMessage("Recording reset. Ready to start.", "green");
          const startButton = document.getElementById("startButton");
          if (startButton) startButton.disabled = false;
          stopButton.disabled = true;
          const pauseResumeButton = document.getElementById("pauseResumeButton");
          if (pauseResumeButton) pauseResumeButton.disabled = true;
          logInfo("No audio frames processed after safeProcessAudioChunk. Full reset performed.");
          processedAnyAudioFrames = false;
          return;
        } else {
          finalChunkProcessed = true;
          finalizeStop();
          logInfo("Stop button processed; final chunk handled.");
        }
      }
    }
  });
}

export { initRecording };
