// Chunked readers keep hours of WAV/FLAC out of a single decoded AudioBuffer.
const text = bytes => new TextDecoder().decode(bytes);
const fourCC = (view, at) => text(new Uint8Array(view.buffer, view.byteOffset + at, 4));
function checkFlacErrors(decoded) {
  const errors = decoded.errors;
  if (!Array.isArray(errors) || errors.length) throw new Error('FLAC decoding failed; the audio was not uploaded.');
}

export async function wavFormat(file) {
  if (file.size < 12) return null;
  const head = new DataView(await file.slice(0, 12).arrayBuffer());
  if (fourCC(head, 0) !== 'RIFF' || fourCC(head, 8) !== 'WAVE') return null;
  const end = head.getUint32(4, true) + 8;
  if (end !== file.size) throw new Error('The WAV file is incomplete.');
  let at = 12, format, data, chunks = 0;
  while (at + 8 <= end && ++chunks <= 4096) {
    const header = new DataView(await file.slice(at, at + 8).arrayBuffer());
    const id = fourCC(header, 0), size = header.getUint32(4, true), next = at + 8 + size + size % 2;
    if (next > end) throw new Error('The WAV file contains a truncated chunk.');
    if (id === 'fmt ' && size >= 16) {
      const fmt = new DataView(await file.slice(at + 8, at + 8 + Math.min(size, 40)).arrayBuffer());
      let encoding = fmt.getUint16(0, true);
      // PCM / IEEE float WAVE_FORMAT_EXTENSIBLE, with the standard subtype GUID.
      if (encoding === 0xfffe && size >= 40 && fmt.getUint16(16, true) >= 22 &&
          fmt.getUint32(28, true) === 0x00100000 && fmt.getUint32(32, false) === 0x800000aa && fmt.getUint32(36, false) === 0x00389b71)
        encoding = fmt.getUint32(24, true);
      format = { encoding, channels: fmt.getUint16(2, true), sampleRate: fmt.getUint32(4, true),
        align: fmt.getUint16(12, true), bits: fmt.getUint16(14, true) };
    } else if (id === 'data') {
      if (data) return null; // Let the browser decode unusual multiple-data WAVs.
      data = { start: at + 8, size };
    }
    at = next;
  }
  if (at !== end || !format || !data) throw new Error('The WAV file has no readable audio data.');
  const { encoding, channels, sampleRate, align, bits } = format;
  if (![1, 3].includes(encoding) || !(encoding === 1 ? [8, 16, 24, 32] : [32, 64]).includes(bits)) return null;
  if (channels < 1 || channels > 32 || sampleRate < 1000 || sampleRate > 384000 || align !== channels * bits / 8 || data.size % align)
    throw new Error('The WAV audio format is invalid.');
  return { ...format, ...data };
}

async function* wavChunks(file, format) {
  const { start, size, channels, sampleRate, align, bits, encoding } = format;
  const bytesPerSample = bits / 8, chunkBytes = Math.max(align, Math.floor(262144 / align) * align);
  for (let at = 0; at < size; at += chunkBytes) {
    const view = new DataView(await file.slice(start + at, start + Math.min(size, at + chunkBytes)).arrayBuffer());
    const channelData = Array.from({ length: channels }, () => new Float32Array(view.byteLength / align));
    for (let i = 0; i < channelData[0].length; i++) for (let ch = 0; ch < channels; ch++) {
      const offset = i * align + ch * bytesPerSample;
      let value;
      if (encoding === 3) value = bits === 32 ? view.getFloat32(offset, true) : view.getFloat64(offset, true);
      else if (bits === 8) value = (view.getUint8(offset) - 128) / 128;
      else if (bits === 16) value = view.getInt16(offset, true) / 32768;
      else if (bits === 24) value = (view.getUint8(offset) | view.getUint8(offset + 1) << 8 | view.getInt8(offset + 2) << 16) / 8388608;
      else value = view.getInt32(offset, true) / 2147483648;
      if (!Number.isFinite(value)) throw new Error('The file contains invalid audio samples.');
      channelData[ch][i] = Math.max(-1, Math.min(1, value));
    }
    yield { channelData, sampleRate, progress: Math.min(1, (at + view.byteLength) / size) };
  }
}

export async function* decodeFileChunks(file, { flacDecoder, decodeOther } = {}) {
  const format = await wavFormat(file);
  if (format) { yield* wavChunks(file, format); return; }
  if (file.size >= 42 && text(new Uint8Array(await file.slice(0, 4).arrayBuffer())) === 'fLaC') {
    const header = new DataView(await file.slice(0, 42).arrayBuffer());
    if ((header.getUint8(4) & 127) !== 0 || header.getUint32(4, false) % 16777216 !== 34)
      throw new Error('The FLAC stream header is invalid.');
    const packed = header.getBigUint64(18, false), expected = Number(packed & ((1n << 36n) - 1n));
    const rate = Number(packed >> 44n), channels = Number(packed >> 41n & 7n) + 1;
    const decoder = await flacDecoder(); let samples = 0;
    try {
      // Small compressed chunks also bound expansion of long CONSTANT frames.
      const chunkBytes = 2048;
      for (let at = 0; at < file.size; at += chunkBytes) {
        const decoded = await decoder.decode(new Uint8Array(await file.slice(at, at + chunkBytes).arrayBuffer()));
        checkFlacErrors(decoded);
        if (decoded.samplesDecoded) {
          if (decoded.sampleRate !== rate || decoded.channelData.length !== channels) throw new Error('The FLAC audio format changed.');
          samples += decoded.samplesDecoded;
          yield { ...decoded, progress: Math.min(1, (at + chunkBytes) / file.size) };
        }
      }
      const tail = await decoder.flush();
      checkFlacErrors(tail);
      if (tail.samplesDecoded) { samples += tail.samplesDecoded; yield { ...tail, progress: 1 }; }
      if (!samples || expected && samples !== expected) {
        const error = new Error('The FLAC audio is empty or incomplete.');
        // Some valid very short CONSTANT frames are not emitted by codec-parser.
        // A browser-decoder retry must recover the complete declared sample count.
        if (expected) error.nativeExpected = Math.round(expected * 16000 / rate);
        throw error;
      }
    } finally { decoder.free(); }
    return;
  }
  yield* decodedChunks(await decodeOther());
}

export async function* decodedChunks(decoded) {
  if (!decoded.channelData?.length || !decoded.channelData[0].length) throw new Error('The audio file is empty.');
  for (let at = 0; at < decoded.channelData[0].length; at += 65536)
    yield { channelData: decoded.channelData.map(channel => channel.subarray(at, at + 65536)),
      sampleRate: decoded.sampleRate, progress: Math.min(1, (at + 65536) / decoded.channelData[0].length) };
}
