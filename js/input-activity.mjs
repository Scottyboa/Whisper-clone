// Input activity is a sound-level indication, not a speech or microphone-health
// verdict. Keep only a timestamp; never retain samples for this feature.
export const INPUT_ACTIVITY_VERSION = 1;
export const INPUT_SOUND_RMS = 0.001; // -60 dBFS; reject silence and very faint input.

export function hasInputSound(samples) {
  if (!samples?.length) return false;
  let energy = 0;
  for (const value of samples) {
    if (!Number.isFinite(value)) return false;
    energy += value * value;
  }
  return energy / samples.length >= INPUT_SOUND_RMS * INPUT_SOUND_RMS;
}

export function inputActivityInfo(value, latestAt) {
  if (value?.inputActivityVersion !== INPUT_ACTIVITY_VERSION) return {};
  const at = value.lastSoundAt;
  if (at !== null && (!Number.isFinite(at) || at <= 0 || at > latestAt)) return {};
  return { inputActivityVersion: INPUT_ACTIVITY_VERSION, lastSoundAt: at };
}

export function inputActivityLabel(value, now = Date.now()) {
  const activity = inputActivityInfo(value, now + 5000);
  if (!activity.inputActivityVersion) return 'Sound activity unavailable';
  if (activity.lastSoundAt === null) return 'No sound detected yet';
  const date = new Date(activity.lastSoundAt), today = new Date(now);
  const pad = n => String(n).padStart(2, '0');
  const time = `${pad(date.getHours())}:${pad(date.getMinutes())}:${pad(date.getSeconds())}`;
  const day = `${date.getFullYear()}-${pad(date.getMonth() + 1)}-${pad(date.getDate())}`;
  const sameDay = date.getFullYear() === today.getFullYear() && date.getMonth() === today.getMonth() && date.getDate() === today.getDate();
  const seconds = Math.max(0, Math.floor((now - activity.lastSoundAt) / 1000));
  const age = seconds < 60 ? `${seconds}s` : seconds < 3600 ? `${Math.floor(seconds / 60)}m` :
    `${Math.floor(seconds / 3600)}h ${Math.floor(seconds / 60) % 60}m`;
  return `${sameDay ? '' : day + ' '}${time} · ${age} ago`;
}
