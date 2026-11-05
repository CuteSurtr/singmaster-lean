"""Build a live.lean-lang.org URL with `codez=` (LZString.compressToBase64, '=' padding removed)."""
import sys
import urllib.parse

KEY = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/="


def compress(s, bits, char):
    if not s:
        return ""
    dictionary, to_create = {}, set()
    w, size, enlarge, nbits = "", 3, 2, 2
    out, val, pos = [], 0, 0

    def emit(value, n):
        nonlocal val, pos
        for _ in range(n):
            val = (val << 1) | (value & 1)
            if pos == bits - 1:
                pos = 0
                out.append(char(val))
                val = 0
            else:
                pos += 1
            value >>= 1

    def emit_w():
        nonlocal enlarge, nbits
        if w in to_create:
            code = ord(w[0])
            if code < 256:
                emit(0, nbits)
                emit(code, 8)
            else:
                emit(1, nbits)
                emit(code, 16)
            enlarge -= 1
            if enlarge == 0:
                enlarge = 2 ** nbits
                nbits += 1
            to_create.discard(w)
        else:
            emit(dictionary[w], nbits)
        enlarge -= 1
        if enlarge == 0:
            enlarge = 2 ** nbits
            nbits += 1

    for c in s:
        if c not in dictionary:
            dictionary[c] = size
            size += 1
            to_create.add(c)
        wc = w + c
        if wc in dictionary:
            w = wc
        else:
            emit_w()
            dictionary[wc] = size
            size += 1
            w = c
    if w != "":
        emit_w()
    emit(2, nbits)
    while True:
        val <<= 1
        if pos == bits - 1:
            out.append(char(val))
            break
        pos += 1
    return "".join(out)


def main():
    src, project, dest = sys.argv[1], sys.argv[2], sys.argv[3]
    code = open(src, encoding="utf-8").read()
    assert all(ord(ch) < 0x10000 for ch in code), "non-BMP character"
    z = compress(code, 6, lambda a: KEY[a]).rstrip("=")
    url = f"https://live.lean-lang.org/#project={project}&codez={urllib.parse.quote(z, safe='')}"
    open(dest, "w").write(url)
    print(len(code), len(url))


if __name__ == "__main__":
    main()
