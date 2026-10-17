import { encodeTimelineFlac, prepareTimelineFlac } from './timeline-flac.mjs?v=20261017-flac1';

self.onmessage = async ({ data }) => {
  try {
    const progress = value => self.postMessage({ progress: value });
    const result = data.action === 'encode' ? await encodeTimelineFlac(data.input, progress) :
      data.action === 'prepare' ? await prepareTimelineFlac(data.input, progress) : null;
    if (!result) throw new Error('Unsupported audio task.');
    self.postMessage({ result });
  } catch (error) { self.postMessage({ error: error.message || 'Audio processing failed.' }); }
};
