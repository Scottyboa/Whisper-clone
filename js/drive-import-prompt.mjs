export function createDriveImportPrompt({dialog, paste, zip, apply, close}) {
  let resolve = null;
  const update = () => {
    const selected = paste.checked || zip.checked;
    apply.textContent = selected ? 'Import' : 'Exit';
    apply.classList.toggle('primary', selected);
  };
  const finish = value => {
    const done = resolve; resolve = null;
    dialog.close(); done?.(value);
  };
  paste.addEventListener('change', update); zip.addEventListener('change', update);
  apply.addEventListener('click', () => finish(paste.checked || zip.checked ? {paste:paste.checked,zip:zip.checked} : null));
  close.addEventListener('click', () => finish(null));
  dialog.addEventListener('cancel', event => { event.preventDefault(); finish(null); });
  dialog.addEventListener('close', () => { const done=resolve;resolve=null;done?.(null); });
  return () => {
    if (resolve) return Promise.resolve(null);
    paste.checked = true; zip.checked = true; update();
    return new Promise(done => { resolve=done;dialog.showModal();apply.focus(); });
  };
}
