#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Собирает «лёгкую» сборку pyWDTT-universal.py из pyWDTT.pyw.

Один и тот же код, но без вшитых колёс: файл меньше в ~20 раз, запускается
на Windows, Linux и macOS, криптография берётся из системного пакета
`cryptography` (если он есть), иначе работает встроенная реализация на чистом
Python. Ничего не скачивается во время работы.

    python3 build_lite.py            # pyWDTT.pyw → pyWDTT-universal.py
    python3 build_lite.py --check    # только посчитать размер и хеш
"""
import hashlib
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, "pyWDTT.pyw")
OUT = os.path.join(HERE, "pyWDTT-universal.py")

# блоки с полезной нагрузкой: base64-колёса и их контрольные суммы
BLOCKS = (
    re.compile(r"^_BUNDLED_WHEELS = \{.*?^\}\n", re.S | re.M),
    re.compile(r"^_BUNDLED_SHA256 = \{.*?^\}\n", re.S | re.M),
)
EMPTY = {0: "_BUNDLED_WHEELS = {}\n", 1: "_BUNDLED_SHA256 = {}\n"}


def build():
    src = open(SRC, encoding="utf-8").read()
    out = src
    for index, pattern in enumerate(BLOCKS):
        out, count = pattern.subn(EMPTY[index], out, count=1)
        if count != 1:
            raise SystemExit("не найден блок №%d — формат pyWDTT.pyw изменился" % index)
    if "_BUNDLED_WHEELS = {}" not in out:
        raise SystemExit("не удалось очистить встроенные колёса")
    open(OUT, "w", encoding="utf-8").write(out)
    try:
        os.chmod(OUT, 0o755)
    except OSError:
        pass
    return src, out


def report(path, size_before=None):
    data = open(path, "rb").read()
    text = "%.2f МБ" % (len(data) / 1048576.0)
    line = "%s: %s · %d строк · sha256 %s" % (
        os.path.basename(path), text, data.count(b"\n") + 1,
        hashlib.sha256(data).hexdigest())
    if size_before:
        line += " · экономия %d%%" % (100 - int(len(data) * 100 / size_before))
    print(line)


if __name__ == "__main__":
    if "--check" not in sys.argv:
        build()
    report(OUT, os.path.getsize(SRC))
