export function createSecondaryPrompt({dialog, summary, transcribe, download, apply, cancel, close}) {
  let resolve = null;
  const update = () => {
    const selected = transcribe.checked || download.checked;
    apply.textContent = selected ? 'Merge and transcribe' : 'Exit';
    apply.classList.toggle('primary', selected);
  };
  const finish = value => {
    const done = resolve; resolve = null;
    dialog.close(); done?.(value);
  };
  for (const [input, other] of [[transcribe, download], [download, transcribe]]) {
    input.addEventListener('change', () => {
      if (input.checked) other.checked = false;
      update();
    });
  }
  apply.addEventListener('click', () => {
    finish(transcribe.checked || download.checked ? {download:download.checked} : null);
  });
  cancel.addEventListener('click', () => finish(null));
  close.addEventListener('click', () => finish(null));
  dialog.addEventListener('cancel', event => { event.preventDefault(); finish(null); });
  dialog.addEventListener('close', () => {
    // A queued close event from the previous prompt must not cancel a newly
    // opened prompt if it was reopened before that event was dispatched.
    if (dialog.open) return;
    const done = resolve; resolve = null; done?.(null);
  });
  const show = text => {
    if (resolve) return Promise.resolve(null);
    summary.textContent = text;
    transcribe.checked = false; download.checked = true; update();
    return new Promise(done => { resolve = done; dialog.showModal(); apply.focus(); });
  };
  show.cancel = () => finish(null);
  return show;
}
