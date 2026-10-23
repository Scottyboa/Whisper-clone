// Private CDP pipes for disposable local test browsers only.
export function protocol(process) {
  let id = 0, buffered = Buffer.alloc(0), closed = false; const pending = new Map();
  const stop = () => {
    closed = true;
    for (const task of pending.values()) { clearTimeout(task.timer); task.reject(new Error('Test browser exited.')); }
    pending.clear();
  };
  process.once('exit', stop); process.once('error', stop);
  process.stdio[3].on('error', stop); process.stdio[4].on('error', stop);
  process.stdio[4].on('data', bytes => {
    buffered = Buffer.concat([buffered, bytes]); let end;
    while ((end = buffered.indexOf(0)) >= 0) {
      const packet = JSON.parse(buffered.subarray(0, end).toString()); buffered = buffered.subarray(end + 1);
      const task = pending.get(packet.id);
      if (task) { pending.delete(packet.id); clearTimeout(task.timer); packet.error ? task.reject(new Error(packet.error.message)) : task.resolve(packet.result); }
    }
  });
  return (method, params = {}, sessionId) => new Promise((resolve, reject) => {
    if (closed) { reject(new Error('Test browser is closed.')); return; }
    const number = ++id;
    const timer = setTimeout(() => { pending.delete(number); reject(new Error(`CDP timeout: ${method}`)); }, 30000);
    pending.set(number, { resolve, reject, timer });
    process.stdio[3].write(JSON.stringify({ id: number, method, params, ...(sessionId ? { sessionId } : {}) }) + '\0');
  });
}

