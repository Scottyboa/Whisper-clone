// recording.js
// Updated recording module to use Speechmatics Real-Time WebSocket API
// processing audio chunks using OfflineAudioContext,
// and streaming transcripts live via a WebSocket, instead of batch jobs.

function hashString(str) {
  let hash = 0;
  for (let i = 0; i < str.length; i++) {
    const char = str.charCodeAt(i);
    hash = ((hash << 5) - hash) + char;
    hash |= 0; // Convert to 32-bit signed integer
  }
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

// --- Real-Time Speechmatics WebSocket Client ---
class RealTimeTranscriber {
  constructor({ apiKey, onTranscript, language = "en" }) {
    this.apiKey = apiKey;
    this.onTranscript = onTranscript;
    this.language = language;
    this.ws = null;
  }

  connect() {
    return new Promise((resolve, reject) => {
      this.ws = new WebSocket(
        "wss://asr.api.speechmatics.com/v2/streaming/ws?auth_token=" + this.apiKey
      );
      this.ws.binaryType = "arraybuffer";

      this.ws.onopen = () => {
        const startMsg = {
          type: "Start",
          data: {
            transcription_config: {
              language: this.language,
              operating_point: "standard",
              enable_partials: true,
              max_delay: 0.7
            }
          }
        };
        this.ws.send(JSON.stringify(startMsg));
        resolve();
      };

      this.ws.onerror = err => {
        logError("RealTimeTranscriber WebSocket error:", err);
        reject(err);
      };

      this.ws.onmessage = ({ data }) => {
        let msg;
        try {
          msg = JSON.parse(new TextDecoder().decode(data));
        } catch (e) {
          logError("Failed to parse WS message:", e);
          return;
        }
        if (msg.type === "Partial") {
          this.onTranscript(msg.data.partial, false);
        } else if (msg.type === "Final") {
          this.onTranscript(msg.data.transcript, true);
        }
      };
    });
  }

  sendAudio(buffer) {
    if (this.ws && this.ws.readyState === WebSocket.OPEN) {
      this.ws.send(buffer);
    }
  }

  stop() {
    if (this.ws && this.ws.readyState === WebSocket.OPEN) {
      this.ws.send(JSON.stringify({ type: "Stop" }));
    }
  }

  disconnect() {
    if (this.ws) this.ws.close();
    this.ws = null;
  }
}

// --- Recording & Processing Variables ---
const MIN_CHUNK_DURATION = 120000;
const MAX_CHUNK_DURATION = 120000;
const watchdogThreshold = 1500;

let mediaStream = null;
let audioReader = null;
let processingTimer = null;
let recordingStartTime = 0;
let accumulatedRecordingTime = 0;
let recordingTimerInterval = null;
let completionTimerInterval = null;
let manualStop = false;
let recordingPaused = false;
let audioFrames = [];
let chunkStartTime = 0;
let lastFrameTime = 0;
let chunkTimeoutId = null;
let chunkProcessingLock = false;
let pendingStop = false;
let finalChunkProcessed = false;

// Real-time transcription instances
let rtTranscriber = null;
let accumulatedTranscript = "";

// --- Utility Functions ---
function updateStatusMessage(message, color = "#333") {
  const el = document.getElementById("statusMessage");
  if (el) {
    el.innerText = message;
    el.style.color = color;
  }
}

function formatTime(ms) {
  const totalSec = Math.floor(ms / 1000);
  if (totalSec < 60) return `${totalSec} sec`;
  const minutes = Math.floor(totalSec / 60);
  const seconds = totalSec % 60;
  return `${minutes} min${seconds ? ` ${seconds} sec` : ""}`;
}

function updateRecordingTimer() {
  const elapsed = accumulatedRecordingTime + (Date.now() - recordingStartTime);
  const el = document.getElementById("recordTimer");
  if (el) el.innerText = "Recording Timer: " + formatTime(elapsed);
}

function stopMicrophone() {
  if (mediaStream) {
    mediaStream.getTracks().forEach(t => t.stop());
    mediaStream = null;
    logInfo("Microphone stopped.");
  }
  if (audioReader) {
    audioReader.cancel();
    audioReader = null;
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
  function writeString(offset, str) {
    for (let i = 0; i < str.length; i++) {
      view.setUint8(offset + i, str.charCodeAt(i));
    }
  }
  writeString(0, "RIFF");
  view.setUint32(4, 36 + samples.length * 2, true);
  writeString(8, "WAVE");
  writeString(12, "fmt ");
  view.setUint32(16, 16, true);
  view.setUint16(20, 1, true);
  view.setUint16(22, numChannels, true);
  view.setUint32(24, sampleRate, true);
  view.setUint32(28, sampleRate * numChannels * 2, true);
  view.setUint16(32, numChannels * 2, true);
  view.setUint16(34, 16, true);
  writeString(36, "data");
  view.setUint32(40, samples.length * 2, true);
  let offset = 44;
  for (let i = 0; i < samples.length; i++, offset += 2) {
    view.setInt16(offset, samples[i], true);
  }
  return new Blob([view], { type: "audio/wav" });
}

async function processAudioUsingOfflineContext(pcmFloat32, originalSampleRate, numChannels) {
  const targetSampleRate = 16000;
  const numFrames = pcmFloat32.length / numChannels;
  const tempCtx = new AudioContext();
  const originalBuffer = tempCtx.createBuffer(numChannels, numFrames, originalSampleRate);
  if (numChannels === 1) {
    originalBuffer.copyToChannel(pcmFloat32, 0);
  } else {
    for (let ch = 0; ch < numChannels; ch++) {
      const channelData = new Float32Array(numFrames);
      for (let i = 0; i < numFrames; i++) {
        channelData[i] = pcmFloat32[i * numChannels + ch];
      }
      originalBuffer.copyToChannel(channelData, ch);
    }
  }
  tempCtx.close();
  const duration = originalBuffer.duration;
  const offlineCtx = new OfflineAudioContext(1, targetSampleRate * duration, targetSampleRate);
  const source = offlineCtx.createBufferSource();
  source.buffer = originalBuffer;
  const gainNode = offlineCtx.createGain();
  const fade = 0.3;
  gainNode.gain.setValueAtTime(0, 0);
  gainNode.gain.linearRampToValueAtTime(1, fade);
  const fadeOut = Math.max(0, duration - fade);
  gainNode.gain.setValueAtTime(1, fadeOut);
  gainNode.gain.linearRampToValueAtTime(0, duration);
  source.connect(gainNode).connect(offlineCtx.destination);
  source.start(0);
  const rendered = await offlineCtx.startRendering();
  const data = rendered.getChannelData(0);
  const int16 = floatTo16BitPCM(data);
  return encodeWAV(int16, targetSampleRate, 1);
}

async function processAudioChunkInternal(force = false) {
  if (!audioFrames.length) return;
  logInfo(`Processing ${audioFrames.length} audio frames`);
  const start = Date.now();
  const frames = audioFrames.splice(0);
  const sampleRate = frames[0].sampleRate;
  const numChannels = frames[0].numberOfChannels;
  let pcmArr = [];
  for (const frame of frames) {
    const n = frame.numberOfFrames;
    if (numChannels === 1) {
      const arr = new Float32Array(n);
      frame.copyTo(arr, { planeIndex: 0 });
      pcmArr.push(arr);
    } else {
      const temp = [];
      for (let c = 0; c < numChannels; c++) {
        const arr = new Float32Array(n);
        frame.copyTo(arr, { planeIndex: c });
        temp.push(arr);
      }
      const inter = new Float32Array(n * numChannels);
      for (let i = 0; i < n; i++)
        for (let c = 0; c < numChannels; c++)
          inter[i * numChannels + c] = temp[c][i];
      pcmArr.push(inter);
    }
    frame.close();
  }
  const totalLen = pcmArr.reduce((s, a) => s + a.length, 0);
  const pcmFloat = new Float32Array(totalLen);
  let off = 0;
  for (const a of pcmArr) {
    pcmFloat.set(a, off);
    off += a.length;
  }
  const wavBlob = await processAudioUsingOfflineContext(pcmFloat, sampleRate, numChannels);
  const wavBuf = await wavBlob.arrayBuffer();
  rtTranscriber.sendAudio(wavBuf);
  logDebug(`Chunk processed in ${Date.now() - start} ms`);
}

async function safeProcessAudioChunk(force = false) {
  if (chunkProcessingLock) return;
  chunkProcessingLock = true;
  await processAudioChunkInternal(force);
  chunkProcessingLock = false;
  if (pendingStop) {
    pendingStop = false;
    finalizeStop();
  }
}

function scheduleChunk() {
  if (manualStop || recordingPaused) return;
  const elapsed = Date.now() - chunkStartTime;
  const sinceLast = Date.now() - lastFrameTime;
  if (elapsed >= MAX_CHUNK_DURATION || (elapsed >= MIN_CHUNK_DURATION && sinceLast >= watchdogThreshold)) {
    safeProcessAudioChunk();
    chunkStartTime = Date.now();
  } else {
    chunkTimeoutId = setTimeout(scheduleChunk, 500);
  }
}

function finalizeStop() {
  const start = Date.now();
  completionTimerInterval = setInterval(() => {
    const el = document.getElementById("transcribeTimer");
    if (el) el.innerText = "Completion Timer: " + formatTime(Date.now() - start);
  }, 500);
  updateStatusMessage("Transcription finished!", "green");
  rtTranscriber.stop();
  setTimeout(() => rtTranscriber.disconnect(), 500);
}

function resetRecordingState() {
  clearTimeout(chunkTimeoutId);
  clearInterval(recordingTimerInterval);
  clearInterval(completionTimerInterval);
  audioFrames = [];
  manualStop = false;
  recordingPaused = false;
  pendingStop = false;
  finalChunkProcessed = false;
  accumulatedRecordingTime = 0;
  accumulatedTranscript = "";
}

function initRecording() {
  const startButton = document.getElementById("startButton");
  const stopButton = document.getElementById("stopButton");
  const pauseButton = document.getElementById("pauseResumeButton");
  const transcriptionElem = document.getElementById("transcription");
  if (!startButton || !stopButton || !pauseButton || !transcriptionElem) return;

  startButton.addEventListener("click", async () => {
    const apiKey = sessionStorage.getItem("user_api_key");
    if (!apiKey) return alert("API key required");
    resetRecordingState();
    transcriptionElem.value = "";

    rtTranscriber = new RealTimeTranscriber({
      apiKey,
      language: "en",
      onTranscript: (text, isFinal) => {
        if (isFinal) accumulatedTranscript += text + " ";
        transcriptionElem.value = accumulatedTranscript + (isFinal ? "" : text);
      }
    });
    await rtTranscriber.connect();

    try {
      mediaStream = await navigator.mediaDevices.getUserMedia({ audio: true });
      recordingStartTime = Date.now();
      recordingTimerInterval = setInterval(updateRecordingTimer, 1000);

      const track = mediaStream.getAudioTracks()[0];
      const processor = new MediaStreamTrackProcessor({ track });
      audioReader = processor.readable.getReader();

      function readLoop() {
        audioReader.read().then(({ done, value }) => {
          if (done) return;
          lastFrameTime = Date.now();
          audioFrames.push(value);
          readLoop();
        }).catch(err => logError("Audio read error:", err));
      }
      readLoop();
      chunkStartTime = Date.now();
      scheduleChunk();

      startButton.disabled = true;
      stopButton.disabled = false;
      pauseButton.disabled = false;
      updateStatusMessage("Recording...", "green");
      logInfo("Recording started.");
    } catch (err) {
      logError("Recording start error:", err);
      updateStatusMessage("Mic error: " + err, "red");
    }
  });

  pauseButton.addEventListener("click", async () => {
    if (!recordingPaused) {
      await safeProcessAudioChunk(false);
      accumulatedRecordingTime += Date.now() - recordingStartTime;
      stopMicrophone();
      recordingPaused = true;
      clearInterval(recordingTimerInterval);
      updateStatusMessage("Recording paused", "orange");
    } else {
      mediaStream = await navigator.mediaDevices.getUserMedia({ audio: true });
      recordingStartTime = Date.now();
      recordingTimerInterval = setInterval(updateRecordingTimer, 1000);
      readLoop();
      scheduleChunk();
      recordingPaused = false;
      updateStatusMessage("Recording...", "green");
    }
  });

  stopButton.addEventListener("click", async () => {
    manualStop = true;
    clearInterval(recordingTimerInterval);
    stopMicrophone();
    if (recordingPaused) {
      finalizeStop();
    } else {
      if (chunkProcessingLock) {
        pendingStop = true;
      } else {
        await safeProcessAudioChunk(true);
        finalizeStop();
      }
    }
  });
}

export { initRecording };
