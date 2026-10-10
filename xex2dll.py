#!/usr/bin/env python3
"""
xex2dll.py - convert Xbox 360 XEX plugins into Xbox 360 DLL modules.

An Xbox 360 "DLL" is still an XEX container: the module-flags field in the XEX
header marks it as a DLL module (flag 0x08) instead of a title/executable
(flag 0x01). This tool sets exactly that and saves the result as <name>.dll.
Nothing is decrypted or recompressed, so it works on every XEX (encrypted,
LZX-compressed, retail or devkit) and cannot fail on a damaged image.

Double-click to open the app window, or from a terminal:
  python xex2dll.py input.xex [output.dll] [--pe]

--pe (advanced) additionally saves the decrypted/decompressed PE image as
<name>.pe.bin for inspection.
"""
import struct
import sys
from pathlib import Path


class XexError(Exception):
    pass

def _fail(msg):
    raise XexError(msg)

_log = print
def log(msg):
    _log(msg)

# ---------------------------------------------------------------- AES-128 ---
def _build_tables():
    sbox = [0] * 256
    p = q = 1
    while True:
        p = p ^ ((p << 1) & 0xFF) ^ (0x1B if p & 0x80 else 0)
        q ^= q << 1; q ^= q << 2; q ^= q << 4; q &= 0xFF
        if q & 0x80:
            q ^= 0x09
        x = q ^ ((q << 1) | (q >> 7)) & 0xFF ^ ((q << 2) | (q >> 6)) & 0xFF \
            ^ ((q << 3) | (q >> 5)) & 0xFF ^ ((q << 4) | (q >> 4)) & 0xFF
        sbox[p] = (x ^ 0x63) & 0xFF
        if p == 1:
            break
    sbox[0] = 0x63
    inv = [0] * 256
    for i, v in enumerate(sbox):
        inv[v] = i
    return sbox, inv

SBOX, INV_SBOX = _build_tables()

def _xt(a):
    return ((a << 1) ^ 0x1B) & 0xFF if a & 0x80 else a << 1

def _mul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        a = _xt(a); b >>= 1
    return r

_M9  = [_mul(i, 9)  for i in range(256)]
_M11 = [_mul(i, 11) for i in range(256)]
_M13 = [_mul(i, 13) for i in range(256)]
_M14 = [_mul(i, 14) for i in range(256)]

def _expand_key(key):
    w = list(key)
    rcon = 1
    for i in range(16, 176, 4):
        t = w[i - 4:i]
        if i % 16 == 0:
            t = [SBOX[t[1]] ^ rcon, SBOX[t[2]], SBOX[t[3]], SBOX[t[0]]]
            rcon = _xt(rcon)
        w += [w[i - 16 + j] ^ t[j] for j in range(4)]
    return [w[r * 16:(r + 1) * 16] for r in range(11)]

def _decrypt_block(rk, blk):
    s = [b ^ k for b, k in zip(blk, rk[10])]
    for rnd in range(9, -1, -1):
        # inv shift rows
        s = [s[0], s[13], s[10], s[7], s[4], s[1], s[14], s[11],
             s[8], s[5], s[2], s[15], s[12], s[9], s[6], s[3]]
        s = [INV_SBOX[b] for b in s]
        s = [b ^ k for b, k in zip(s, rk[rnd])]
        if rnd:
            o = []
            for c in range(0, 16, 4):
                a0, a1, a2, a3 = s[c:c + 4]
                o += [_M14[a0] ^ _M11[a1] ^ _M13[a2] ^ _M9[a3],
                      _M9[a0] ^ _M14[a1] ^ _M11[a2] ^ _M13[a3],
                      _M13[a0] ^ _M9[a1] ^ _M14[a2] ^ _M11[a3],
                      _M11[a0] ^ _M13[a1] ^ _M9[a2] ^ _M14[a3]]
            s = o
    return bytes(s)

def aes_ecb_decrypt(key, data):
    rk = _expand_key(key)
    return b"".join(_decrypt_block(rk, data[i:i + 16]) for i in range(0, len(data), 16))

def aes_cbc_decrypt(key, data, iv=bytes(16)):
    rk = _expand_key(key)
    out = bytearray()
    prev = iv
    for i in range(0, len(data) - len(data) % 16, 16):
        blk = data[i:i + 16]
        d = _decrypt_block(rk, blk)
        out += bytes(a ^ b for a, b in zip(d, prev))
        prev = blk
    return bytes(out)

# ------------------------------------------------------------------- LZX ----
class _Bits:
    """LZX bitstream: little-endian 16-bit words, bits consumed MSB-first."""
    def __init__(self, data):
        self.d = data
        self.pos = 0
        self.buf = 0
        self.cnt = 0

    def _fill(self, n):
        d = self.d
        while self.cnt < n:
            p = self.pos
            w = (d[p] | (d[p + 1] << 8)) if p + 1 < len(d) else (d[p] if p < len(d) else 0)
            self.pos = p + 2
            self.buf = (self.buf << 16) | w
            self.cnt += 16

    def bits(self, n):
        if n == 0:
            return 0
        if self.cnt < n:
            self._fill(n)
        self.cnt -= n
        v = self.buf >> self.cnt
        self.buf &= (1 << self.cnt) - 1
        return v

    def decode(self, tree):
        table, maxbits = tree
        if self.cnt < maxbits:
            self._fill(maxbits)
        e = table[self.buf >> (self.cnt - maxbits)]
        if e == 0xFFFFFFFF:
            raise ValueError("LZX: invalid Huffman code")
        n = e & 31
        self.cnt -= n
        self.buf &= (1 << self.cnt) - 1
        return e >> 5

    def align_frame(self):
        drop = self.cnt & 15
        self.cnt -= drop
        self.buf &= (1 << self.cnt) - 1

    def align_for_raw(self):
        consumed = self.pos * 8 - self.cnt
        self.pos = ((consumed // 16) + 1) * 2
        self.buf = 0
        self.cnt = 0


def _make_tree(lens):
    maxb = max(lens) if lens else 0
    if maxb == 0:
        return None
    table = [0xFFFFFFFF] * (1 << maxb)
    code = 0
    for L in range(1, maxb + 1):
        for sym, l in enumerate(lens):
            if l == L:
                lo = code << (maxb - L)
                hi = (code + 1) << (maxb - L)
                if hi > len(table):
                    raise ValueError("LZX: over-subscribed Huffman tree")
                table[lo:hi] = [(sym << 5) | L] * (hi - lo)
                code += 1
        code <<= 1
    return (table, maxb)


def _position_tables(window_bits):
    extra, base = [], [0]
    i = 0
    while True:
        e = 0 if i < 4 else (i >> 1) - 1 if i < 36 else 17
        extra.append(e)
        base.append(base[-1] + (1 << e))
        i += 1
        if base[-1] >= (1 << window_bits):
            break
    return extra, base, len(extra)


class LZXDecoder:
    def __init__(self, window_bits, wim_mode=False):
        self.extra, self.base, self.slots = _position_tables(window_bits)
        self.num_main = 256 + self.slots * 8
        self.main_lens = [0] * self.num_main
        self.len_lens = [0] * 249
        self.R = [1, 1, 1]
        self.wim = wim_mode

    def _read_lengths(self, br, lens, first, last):
        pre = _make_tree([br.bits(4) for _ in range(20)])
        x = first
        while x < last:
            z = br.decode(pre) if pre else 0
            if z == 17:
                y = br.bits(4) + 4
                for k in range(min(y, last - x)): lens[x + k] = 0
                x += y
            elif z == 18:
                y = br.bits(5) + 20
                for k in range(min(y, last - x)): lens[x + k] = 0
                x += y
            elif z == 19:
                y = br.bits(1) + 4
                z = br.decode(pre)
                z = lens[x] - z
                if z < 0: z += 17
                for k in range(min(y, last - x)): lens[x + k] = z
                x += y
            else:
                z = lens[x] - z
                if z < 0: z += 17
                lens[x] = z
                x += 1

    def decompress(self, data, out_size):
        br = _Bits(data)
        out = bytearray(out_size)
        pos = 0
        frame = 0
        header_read = self.wim
        intel_started = self.wim
        intel_filesize = 12000000 if self.wim else 0
        block_remaining = 0
        block_type = 0
        block_length = 0
        main = length = aligned = None
        R = self.R
        extra, base = self.extra, self.base

        while pos < out_size:
            frame_start = frame * 32768
            frame_end = min(frame_start + 32768, out_size)
            while pos < frame_end:
                if block_remaining == 0:
                    if block_type == 3 and (block_length & 1):
                        br.pos += 1
                    if not header_read:
                        if br.bits(1):
                            intel_filesize = (br.bits(16) << 16) | br.bits(16)
                        header_read = True
                    block_type = br.bits(3)
                    if self.wim:  # WIM variant of the block-size field (test harness only)
                        block_length = 32768 if br.bits(1) else br.bits(16)
                    else:
                        block_length = (br.bits(16) << 8) | br.bits(8)
                    block_remaining = block_length
                    if block_type in (1, 2):
                        if block_type == 2:
                            aligned = _make_tree([br.bits(3) for _ in range(8)])
                        self._read_lengths(br, self.main_lens, 0, 256)
                        self._read_lengths(br, self.main_lens, 256, self.num_main)
                        if self.main_lens[0xE8]:
                            intel_started = True
                        main = _make_tree(self.main_lens)
                        self._read_lengths(br, self.len_lens, 0, 249)
                        length = _make_tree(self.len_lens)
                    elif block_type == 3:
                        intel_started = True
                        br.align_for_raw()
                        for i in range(3):
                            p = br.pos
                            R[i] = int.from_bytes(data[p:p + 4], "little")
                            br.pos += 4
                    else:
                        raise ValueError(f"LZX: bad block type {block_type}")

                run = min(block_remaining, frame_end - pos)
                if block_type == 3:
                    p = br.pos
                    out[pos:pos + run] = data[p:p + run]
                    br.pos += run
                    pos += run
                    block_remaining -= run
                    continue

                this_run = run
                while this_run > 0:
                    sym = br.decode(main)
                    if sym < 256:
                        out[pos] = sym
                        pos += 1
                        this_run -= 1
                        continue
                    sym -= 256
                    mlen = sym & 7
                    if mlen == 7:
                        mlen += br.decode(length)
                    mlen += 2
                    slot = sym >> 3
                    if slot == 0:
                        off = R[0]
                    elif slot == 1:
                        off = R[1]; R[1] = R[0]; R[0] = off
                    elif slot == 2:
                        off = R[2]; R[2] = R[0]; R[0] = off
                    else:
                        e = extra[slot]
                        if block_type == 2 and e >= 3:
                            vb = br.bits(e - 3) if e > 3 else 0
                            off = base[slot] - 2 + (vb << 3) + br.decode(aligned)
                        elif e > 0:
                            off = base[slot] - 2 + br.bits(e)
                        else:
                            off = 1
                        R[2] = R[1]; R[1] = R[0]; R[0] = off
                    if off > pos:
                        raise ValueError("LZX: match offset before start of data")
                    mlen = min(mlen, out_size - pos)
                    src = pos - off
                    if off >= mlen:
                        out[pos:pos + mlen] = out[src:src + mlen]
                    else:
                        for k in range(mlen):
                            out[pos + k] = out[src + k]
                    pos += mlen
                    this_run -= mlen
                block_remaining -= (run - this_run)

            br.align_frame()
            # Intel E8 call-translation postprocess
            fsize = frame_end - frame_start
            if intel_started and intel_filesize and frame < 32768 and fsize > 10:
                curpos = frame_start
                i = frame_start
                end = frame_end - 10
                while i < end:
                    if out[i] != 0xE8:
                        i += 1; curpos += 1
                        continue
                    i += 1
                    absoff = int.from_bytes(out[i:i + 4], "little", signed=True)
                    if -curpos <= absoff < intel_filesize:
                        rel = absoff - curpos if absoff >= 0 else absoff + intel_filesize
                        out[i:i + 4] = (rel & 0xFFFFFFFF).to_bytes(4, "little")
                    i += 4
                    curpos += 5
            frame += 1
        return bytes(out)

# --------------------------------------------------------------- XEX2 -------
# Well-known master keys (retail, devkit, XEX1). Each candidate is tried and
# validated by checking for the "MZ" header after decryption.
MASTER_KEYS = {
    "retail": bytes.fromhex("20B185A59D28FDC340583FBB0896BF91"),
    "devkit": bytes(16),
    "xex1":   bytes.fromhex("DAB69AD98E28764F977EE2487E4F3F68"),
}

MACHINE_PPC_BE = 0x01F2

def be32(d, o): return struct.unpack_from(">I", d, o)[0]
def be16(d, o): return struct.unpack_from(">H", d, o)[0]

def parse_xex(d):
    if d[:4] != b"XEX2":
        _fail("Not an XEX2 file (magic is %r)." % d[:4])
    pe_off = be32(d, 0x08)
    sec_off = be32(d, 0x10)
    count = be32(d, 0x14)
    opt = {}
    for i in range(count):
        hid, val = struct.unpack_from(">II", d, 0x18 + i * 8)
        low = hid & 0xFF
        if low in (0, 1):
            opt[hid] = val
        elif low == 0xFF:
            size = be32(d, val)
            opt[hid] = d[val:val + size]
        else:
            opt[hid] = d[val:val + low * 4]
    return pe_off, sec_off, opt

def expand_basic(data, blocks):
    out = bytearray()
    pos = 0
    for dsize, zsize in blocks:
        out += data[pos:pos + dsize]
        pos += dsize
        out += bytes(zsize)
    return bytes(out)


def expand_normal(data, ffi, image_size):
    """XEX 'normal' compression: LZX stream split into blocks of chunks."""
    window_size = be32(ffi, 8)
    window_bits = window_size.bit_length() - 1
    if not 15 <= window_bits <= 21:
        _fail(f"Unexpected LZX window size 0x{window_size:X}.")
    cur_size = be32(ffi, 12)          # first block info comes from the header
    p = 0
    stream = bytearray()
    while cur_size:
        nxt = be32(data, p)           # each block starts with the NEXT block's info
        block_end = p + cur_size
        p += 24                       # size (4) + sha1 (20)
        while True:
            chunk = be16(data, p)
            p += 2
            if chunk == 0:
                break
            stream += data[p:p + chunk]
            p += chunk
        p = block_end
        cur_size = nxt
    return LZXDecoder(window_bits).decompress(bytes(stream), image_size)

def find_pe(img):
    """Locate the PE header. Returns (offset, endian) or None.
    Xbox 360 PEs are big-endian, but both byte orders are tried."""
    if img[:2] != b"MZ" or len(img) < 0x100:
        return None
    hit = None
    for en in (">", "<"):
        lf = struct.unpack_from(en + "I", img, 0x3C)[0]
        if 0 < lf <= len(img) - 24 and img[lf:lf + 4] == b"PE\0\0":
            hit = lf
            break
    if hit is None:  # last resort: scan the header area
        i = img.find(b"PE\0\0", 0x40, 0x4000)
        if i == -1:
            return None
        hit = i
    if struct.unpack_from(">H", img, hit + 4)[0] == MACHINE_PPC_BE:
        return hit, ">"
    if struct.unpack_from("<H", img, hit + 4)[0] == MACHINE_PPC_BE:
        return hit, "<"
    return hit, ">"


def _decode(payload, comp, ffi, image_size):
    if comp == 0:
        return payload
    if comp == 1:
        n = (be32(ffi, 0) - 8) // 8
        blocks = [struct.unpack_from(">II", ffi, 8 + i * 8) for i in range(n)]
        return expand_basic(payload, blocks)
    if comp == 2:
        return expand_normal(payload, ffi, image_size)
    _fail("Delta compression is not supported by this script.")


def extract_image(d):
    pe_off, sec_off, opt = parse_xex(d)
    ffi = opt.get(0x000003FF)
    if ffi is None:
        _fail("File-format info header (0x3FF) missing.")
    enc, comp = be16(ffi, 4), be16(ffi, 6)
    image_size = be32(d, sec_off + 4)
    log(f"XEX: encryption={enc} compression={comp} "
        f"data@0x{pe_off:X} image_size=0x{image_size:X}")
    payload = d[pe_off:]

    if enc == 0:
        img = _decode(payload, comp, ffi, image_size)
        return img, find_pe(img) is not None
    if enc != 1:
        _fail(f"Unknown encryption type {enc}.")

    file_key = d[sec_off + 0x150:sec_off + 0x160]
    sessions = {n: aes_ecb_decrypt(mk, file_key) for n, mk in MASTER_KEYS.items()}

    def probe_ok(session):
        probe = aes_cbc_decrypt(session, payload[:64])
        if comp == 2:
            return be32(probe, 0) <= len(payload) and 0 < be16(probe, 24) <= 0x7FFF
        return probe[:2] == b"MZ"

    names = [n for n, s_ in sessions.items() if probe_ok(s_)]
    if not names:
        names = list(sessions)       # nothing looked right: try every key
    first_result = None
    for name in names:
        try:
            img = _decode(aes_cbc_decrypt(sessions[name], payload), comp, ffi, image_size)
        except Exception as e:       # wrong key can break the LZX stream
            log(f"Key '{name}': decode failed ({e})")
            continue
        if find_pe(img) is not None:
            log(f"Key matched: {name}")
            return img, True
        log(f"Key '{name}': decoded but no valid PE header")
        if first_result is None:
            first_result = img
    if first_result is None:
        _fail("Could not decrypt/decompress this XEX with any known key.")
    return first_result, False


# ---------------------------------------------------------------- PE patch ---
IMAGE_FILE_EXECUTABLE_IMAGE = 0x0002
IMAGE_FILE_DLL = 0x2000

def patch_to_dll(img):
    """Set the DLL flag. Returns patched bytes, or None if no valid PE."""
    pe = find_pe(img)
    if pe is None:
        return None
    lf, en = pe
    img = bytearray(img)
    off = lf + 4 + 18  # COFF Characteristics
    ch = struct.unpack_from(en + "H", img, off)[0] | IMAGE_FILE_DLL | IMAGE_FILE_EXECUTABLE_IMAGE
    struct.pack_into(en + "H", img, off, ch)
    return bytes(img)

def convert_pe(src, dst=None):
    """Advanced: save the decoded PE image (not loadable on the console)."""
    src = Path(src)
    dst = Path(dst) if dst else src.with_suffix(".pe.bin")
    img, valid = extract_image(src.read_bytes())
    out = patch_to_dll(img) or img
    if not valid:
        log("Note: decoded image has no valid PE header (saved as-is).")
    dst.write_bytes(out)
    log(f"Saved decoded PE image: {dst} ({len(out)} bytes)")
    return dst


MODULE_FLAG_TITLE = 0x00000001
MODULE_FLAG_DLL = 0x00000008


def convert(src, dst=None, also_pe=False):
    """XEX -> Xbox 360 DLL module (XEX container with the DLL flag set)."""
    src = Path(src)
    data = bytearray(src.read_bytes())
    if data[:4] not in (b"XEX2", b"XEX1"):
        _fail("not an Xbox 360 XEX file (missing XEX2/XEX1 header).")
    flags = be32(data, 4)
    new_flags = (flags & ~MODULE_FLAG_TITLE) | MODULE_FLAG_DLL
    log(f"{src.name}: module flags 0x{flags:08X} -> 0x{new_flags:08X}"
        + ("  (already a DLL module)" if flags == new_flags else ""))
    struct.pack_into(">I", data, 4, new_flags)
    if dst is None:
        dst = src.with_suffix(".dll")
        if dst == src:                      # input already named .dll
            dst = src.with_name(src.stem + "_xbox.dll")
    dst = Path(dst)
    dst.write_bytes(bytes(data))
    log(f"Wrote {dst} ({len(data)} bytes)")
    if also_pe:
        try:
            convert_pe(src, dst.with_suffix(".pe.bin"))
        except Exception as e:
            log(f"(advanced PE export skipped: {e})")
    return dst


# --------------------------------------------------------------------- GUI ---
def run_gui():
    import threading, queue, os, subprocess
    import tkinter as tk
    from tkinter import ttk, filedialog, messagebox

    root = tk.Tk()
    root.title("XEX to Xbox 360 DLL Converter")
    root.geometry("720x560")
    root.minsize(560, 460)

    files = []
    outdir = tk.StringVar(value="")
    q = queue.Queue()

    frm = ttk.Frame(root, padding=12)
    frm.pack(fill="both", expand=True)

    ttk.Label(frm, text="XEX files (DashLaunch plugins, etc.)").pack(anchor="w")
    lb_frame = ttk.Frame(frm)
    lb_frame.pack(fill="both", expand=False, pady=(4, 8))
    lb = tk.Listbox(lb_frame, height=5, selectmode="extended")
    sb = ttk.Scrollbar(lb_frame, command=lb.yview)
    lb.config(yscrollcommand=sb.set)
    lb.pack(side="left", fill="both", expand=True)
    sb.pack(side="right", fill="y")

    btns = ttk.Frame(frm)
    btns.pack(fill="x")

    def add_files():
        for p in filedialog.askopenfilenames(
                title="Select XEX files",
                filetypes=[("Xbox 360 executables", "*.xex"), ("All files", "*.*")]):
            if p not in files:
                files.append(p)
                lb.insert("end", p)

    def remove_sel():
        for i in reversed(lb.curselection()):
            lb.delete(i)
            del files[i]

    def clear_all():
        lb.delete(0, "end")
        files.clear()

    ttk.Button(btns, text="Add XEX...", command=add_files).pack(side="left")
    ttk.Button(btns, text="Remove", command=remove_sel).pack(side="left", padx=6)
    ttk.Button(btns, text="Clear", command=clear_all).pack(side="left")

    outfrm = ttk.Frame(frm)
    outfrm.pack(fill="x", pady=(10, 0))
    ttk.Label(outfrm, text="Output folder (blank = next to each XEX):").pack(anchor="w")
    row = ttk.Frame(outfrm)
    row.pack(fill="x", pady=(2, 0))
    ttk.Entry(row, textvariable=outdir).pack(side="left", fill="x", expand=True)

    def pick_out():
        d = filedialog.askdirectory(title="Choose output folder")
        if d:
            outdir.set(d)

    ttk.Button(row, text="Browse...", command=pick_out).pack(side="left", padx=(6, 0))

    # Pack the Convert row and progress bar FIRST (anchored to the bottom) so
    # they can never be squeezed out of view by the log box.
    bottom = ttk.Frame(frm)
    bottom.pack(side="bottom", fill="x")
    bar = ttk.Progressbar(frm, mode="determinate")
    bar.pack(side="bottom", fill="x", pady=(8, 8))

    pe_var = tk.BooleanVar(value=False)
    ttk.Checkbutton(frm, text="Also save decoded PE image (advanced, off by default)",
                    variable=pe_var).pack(anchor="w", pady=(8, 0))

    ttk.Label(frm, text="Log").pack(anchor="w", pady=(10, 0))
    logbox = tk.Text(frm, height=6, state="disabled", wrap="word")
    logbox.pack(fill="both", expand=True, pady=(2, 8))

    def append(msg):
        logbox.config(state="normal")
        logbox.insert("end", msg + "\n")
        logbox.see("end")
        logbox.config(state="disabled")

    go = ttk.Button(bottom, text="  CONVERT  ")
    go.pack(side="left")

    def open_out():
        d = outdir.get() or (os.path.dirname(files[0]) if files else "")
        if d and os.path.isdir(d):
            if sys.platform.startswith("win"):
                os.startfile(d)
            elif sys.platform == "darwin":
                subprocess.run(["open", d])
            else:
                subprocess.run(["xdg-open", d])

    ttk.Button(bottom, text="Open output folder", command=open_out).pack(side="left", padx=6)

    def copy_log():
        root.clipboard_clear()
        root.clipboard_append(logbox.get("1.0", "end"))

    ttk.Button(bottom, text="Copy log", command=copy_log).pack(side="left")

    def worker(todo, odir, also_pe):
        global _log
        _log = lambda m: q.put(("log", m))
        ok = 0
        for n, f in enumerate(todo, 1):
            try:
                dst = None
                if odir:
                    dst = Path(odir) / (Path(f).stem + ".dll")
                convert(f, dst, also_pe)
                ok += 1
            except XexError as e:
                q.put(("log", f"ERROR ({Path(f).name}): {e}"))
            except Exception as e:  # keep the app alive no matter what
                q.put(("log", f"ERROR ({Path(f).name}): {type(e).__name__}: {e}"))
            q.put(("progress", n))
        q.put(("done", ok, len(todo)))

    def start():
        if not files:
            messagebox.showinfo("XEX to Xbox DLL", "Add at least one XEX file first.")
            return
        go.config(state="disabled")
        bar.config(maximum=len(files), value=0)
        threading.Thread(target=worker, args=(list(files), outdir.get().strip(), pe_var.get()),
                         daemon=True).start()

    go.config(command=start)

    def poll():
        try:
            while True:
                item = q.get_nowait()
                if item[0] == "log":
                    append(item[1])
                elif item[0] == "progress":
                    bar.config(value=item[1])
                elif item[0] == "done":
                    append(f"Finished: {item[1]}/{item[2]} converted.")
                    go.config(state="normal")
        except queue.Empty:
            pass
        root.after(80, poll)

    append("Ready. Click 'Add XEX...', choose your file(s), then press CONVERT (bottom left).")
    poll()
    root.mainloop()


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    also_pe = "--pe" in sys.argv[1:]
    # No arguments (e.g. double-clicked) -> open the app window.
    if not args:
        try:
            run_gui()
        except Exception as e:
            print(f"Could not start the window: {e}")
            print(__doc__)
            input("Press Enter to close...")
        return
    try:
        convert(args[0], args[1] if len(args) > 1 else None, also_pe)
    except XexError as e:
        print(f"Error: {e}")
        input("Press Enter to close...")
        sys.exit(1)

if __name__ == "__main__":
    main()
