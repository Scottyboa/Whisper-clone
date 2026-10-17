"""Exercise libVLC's real demuxer, decoder and playback clock without a GUI."""
import ctypes as C
import json
import sys
import time

vlc = C.CDLL(sys.argv[1])


def api(name, arguments, result):
    function = getattr(vlc, 'libvlc_' + name)
    function.argtypes = arguments
    function.restype = result
    return function


ptr = C.c_void_p
new = api('new', [C.c_int, C.POINTER(C.c_char_p)], ptr)
media_new = api('media_new_path', [ptr, C.c_char_p], ptr)
player_new = api('media_player_new_from_media', [ptr], ptr)
play = api('media_player_play', [ptr], C.c_int)
state = api('media_player_get_state', [ptr], C.c_int)
length = api('media_player_get_length', [ptr], C.c_longlong)
get_time = api('media_player_get_time', [ptr], C.c_longlong)
set_position = api('media_player_set_position', [ptr, C.c_float], None)
stop = api('media_player_stop', [ptr], None)
player_release = api('media_player_release', [ptr], None)
media_release = api('media_release', [ptr], None)
release = api('release', [ptr], None)
version = api('get_version', [], C.c_char_p)

options = [b'--intf=dummy', b'--aout=dummy', b'--vout=dummy', b'--no-video',
           b'--no-xlib', b'--no-plugins-cache', b'--no-media-library', b'--quiet']
instance = new(len(options), (C.c_char_p * len(options))(*options))
assert instance, 'Cannot initialize VLC'
try:
    for path in sys.argv[2:]:
        medium = media_new(instance, path.encode())
        assert medium, 'Cannot open FLAC'
        player = player_new(medium)
        assert player, 'Cannot create VLC player'
        try:
            assert play(player) == 0, 'VLC could not start playback'
            deadline = time.monotonic() + 4
            while time.monotonic() < deadline:
                if length(player) > 0 and state(player) == 3:
                    break
                time.sleep(.02)
            assert state(player) == 3, 'Playback did not start'
            duration = length(player)
            positions = ([.5, .02, 800.1 / 1800, 10.1 / 1800, .95, 1700.1 / 1800]
                         if duration == 1800000 else [.8, .02, .5])
            sought = []
            for position in positions:
                target = round(duration * position)
                set_position(player, position)
                times = []
                for _ in range(13):
                    time.sleep(.1)
                    times.append(get_time(player))
                # A failed VLC seek falsely reports the requested time while
                # freezing there. Checking just get_time() once misses this bug.
                assert state(player) == 3, (path, target, state(player))
                assert target - 100 <= times[-1] <= target + 4500, (path, target, times)
                assert times[-1] - times[3] >= 400, ('Playback froze after seeking', path, target, times)
                sought.append(target)
            print(json.dumps({'version': version().decode(), 'duration': duration, 'seeks': sought}), flush=True)
        finally:
            stop(player)
            player_release(player)
            media_release(medium)
finally:
    release(instance)
