# Streaming FLAC decoder

`@wasm-audio-decoders/flac` 0.2.11 from npm, bundled as an ES module with
esbuild 0.28.2 without property-name mangling:
https://registry.npmjs.org/@wasm-audio-decoders/flac/-/flac-0.2.11.tgz

`flac-decoder.min.mjs` SHA-256:
`79171140a92c6d4c5921a97cb9141d0bd208cd3e508b52dba020dc7f5c2a9a09`

The standalone JavaScript includes its WASM and dependencies. The companion
source map includes the original JavaScript sources. This separate file can be
replaced with a rebuilt version without changing the application. No user audio
is sent to npm, a CDN, or any decoder service.

To rebuild: in `build`, run `npm ci --ignore-scripts` followed by `node build.mjs`.
The lockfile pins all dependencies. The original package sources are unchanged.

Upstream source, build instructions and libFLAC source/build references:
https://github.com/eshaz/wasm-audio-decoders

Components:

- FLAC decoder and `@wasm-audio-decoders/common` 9.0.7: Ethan Halsall, MIT (`LICENSE`).
- `codec-parser` 2.5.0: Ethan Halsall, LGPL-3.0-or-later
  (`CODEC-PARSER-LICENSE` and `GPL-3.0.txt`). Source:
  https://www.npmjs.com/package/codec-parser/v/2.5.0 and
  https://github.com/eshaz/codec-parser .
- libFLAC: Josh Coalson and Xiph.Org Foundation, BSD (`LIBFLAC-LICENSE`).
- esbuild-generated helpers: Evan Wallace, MIT (`ESBUILD-LICENSE`).
