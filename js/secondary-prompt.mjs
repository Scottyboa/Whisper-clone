export function createSecondaryPrompt({dialog, summary, transcribe, download, autoExport, exportOptions, exportError, folders, apply, cancel, close}) {
  let resolve = null;
  const chosen = () => folders.filter(folder => folder.input.checked).map(folder => folder.name);
  const update = () => {
    const selected = transcribe.checked || download.checked;
    const exporting = selected && autoExport.checked;
    autoExport.disabled = !selected;
    exportOptions.hidden = !exporting;
    folders.forEach(folder => { folder.input.disabled = !exporting; });
    apply.disabled = exporting && !chosen().length;
    exportError.textContent = apply.disabled ? 'Choose at least one OneDrive destination, or turn off automatic export.' : '';
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
  autoExport.addEventListener('change', update);
  folders.forEach(folder => folder.input.addEventListener('change', update));
  apply.addEventListener('click', () => {
    const selected = transcribe.checked || download.checked;
    if (selected && autoExport.checked && !chosen().length) { update(); return; }
    finish(selected ? {download:download.checked, ...(autoExport.checked ? {exportFolders:chosen()} : {})} : null);
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
    transcribe.checked = false; download.checked = true; autoExport.checked = false;
    folders.forEach(folder => { folder.input.checked = !!folder.defaultChecked; });
    update();
    return new Promise(done => { resolve = done; dialog.showModal(); apply.focus(); });
  };
  show.cancel = () => finish(null);
  return show;
}

