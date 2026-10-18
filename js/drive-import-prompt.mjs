export function createDriveImportPrompt({dialog, paste, zip, apply, close, folders = [], title, importOptions, help}) {
  let resolve = null, action = 'import';
  const labels = {import:'Import',export:'Export',clear:'Clear'};
  const chosen = () => folders.filter(folder => folder.input.checked).map(folder => folder.name);
  const update = () => {
    const selected = (!folders.length || chosen().length > 0) && (action !== 'import' || paste.checked || zip.checked);
    apply.textContent = selected ? labels[action] : 'Exit';
    apply.classList.toggle('primary', selected);
  };
  const finish = value => {
    const done = resolve; resolve = null;
    dialog.close(); done?.(value);
  };
  paste.addEventListener('change', update); zip.addEventListener('change', update);
  folders.forEach(folder => folder.input.addEventListener('change', update));
  apply.addEventListener('click', () => {
    const names = chosen();
    finish((!folders.length || names.length) && (action !== 'import' || paste.checked || zip.checked) ?
      {paste:paste.checked,zip:zip.checked,...(folders.length ? {folders:names} : {})} : null);
  });
  close.addEventListener('click', () => finish(null));
  dialog.addEventListener('cancel', event => { event.preventDefault(); finish(null); });
  dialog.addEventListener('close', () => { const done=resolve;resolve=null;done?.(null); });
  return (mode = 'import') => {
    if (resolve) return Promise.resolve(null);
    if (!labels[mode]) return Promise.resolve(null);
    action = mode;
    if (title) title.textContent = `${labels[action]} ${action === 'export' ? 'to' : 'from'} OneDrive`;
    if (importOptions) importOptions.hidden = action !== 'import';
    if (help) help.textContent = action === 'import' ? 'Selected folders are combined into COMPLETE.txt. Inserting replaces the current transcript.' :
      action === 'export' ? 'Save the current text to each selected folder.' : 'Only TXT files directly inside the selected folders are cleared. Confirmation follows.';
    folders.forEach((folder, index) => { folder.input.checked = index === 0; });
    paste.checked = true; zip.checked = true; update();
    return new Promise(done => { resolve=done;dialog.showModal();apply.focus(); });
  };
}
