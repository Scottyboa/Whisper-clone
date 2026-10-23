import { build } from 'esbuild';
import { readFile, writeFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';

const outfile = fileURLToPath(new URL('../flac-decoder.min.mjs', import.meta.url));
await build({ entryPoints: [fileURLToPath(import.meta.resolve('@wasm-audio-decoders/flac'))],
  bundle: true, format: 'esm', platform: 'browser', minify: true,
  sourcemap: 'linked', sourcesContent: true, outfile });
const map = JSON.parse(await readFile(outfile + '.map', 'utf8'));
map.sources = map.sources.map(source => 'npm/' + source.split('node_modules/').at(-1));
await writeFile(outfile + '.map', JSON.stringify(map) + '\n');
