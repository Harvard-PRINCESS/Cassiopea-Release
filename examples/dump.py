#!/usr/bin/env python3

# to run this, run the following command from the top level directory output by benchmark
# find . -name "synth-*.log" -print0 | sort -z | xargs -0 tail -n 1 | python dump.py "x" > out.csv

# the regular expression assumes that relevant outputs are in "x-[machine].log"
# where x should be specified as an argument to the script

import re
import sys
import math

# use cases and their directory names
tests = [
  "IS", "GD", "CD", "CL", "CH", "SA",
  "SJ", "LJ", "CRT-i", "CRT-s", "SYS", "IRQ", "TS", "TS-e", "TS-s", "TS-l", "TS-c"
]
testnames = {
  "IS" : "initial_stack",
  "GD" : "get_disp",
  "CD" : "disp_disabled",
  "CL" : "check_low",
  "CH" : "check_high",
  "SA" : "set_area",
  "SJ" : "setjmp-full",
  "LJ" : "longjmp-full",
  "CRT-i" : "crt0_initregs",
  "CRT-s" : "crt0_savevals",
  "SYS" : "syscalls_loadnum",
  "IRQ" : "cpu_irqoff",
  "TS" : "switch_all",
  "TS-e" : "switch_enter",
  "TS-s" : "switch_save",
  "TS-l" : "switch_load",
  "TS-c" : "switch_leave"
}

# architectures and their directory names
archs = ["ARM", "MIPS", "x86-64"]
archnames = {
  "ARM" : "arm32",
  "MIPS" : "mips",
  "x86-64" : "amd64"
}

lengths = {}
lengths["ARM"] = {
  "IS" : 2,
  "GD" : 3,
  "CD" : 2,
  "CL" : 3,
  "CH" : 4,
  "SA" : 3,
  "SJ" : 12,
  "CRT-i" : 0,
  "CRT-s" : 4,
  "SYS" : 1,
  "IRQ" : 1,
  "TS-e" : 1,
  "TS-s" : 1,
  "TS-l" : 1,
  "TS-c" : 1
}
lengths["MIPS"] = {
  "IS" : 2,
  "GD" : 3,
  "CD" : 2,
  "CL" : 3,
  "CH" : 2,
  "SA" : 3,
  "SJ" : 12,
  "CRT-i" : 1,
  "CRT-s" : 2,
  "SYS" : 1,
  "IRQ" : 3,
  "TS-e" : 1,
  "TS-s" : 1,
  "TS-l" : 1,
  "TS-c" : 1
}
lengths["x86-64"] = {
  "IS" : 1,
  "GD" : 2,
  "CD" : 1,
  "CL" : 1,
  "CH" : 1,
  "SA" : 4,
  "SJ" : 9,
  "CRT-i" : 0,
  "CRT-s" : 2,
  "SYS" : 1,
  "IRQ" : 1,
  "TS-e" : 1,
  "TS-s" : 1,
  "TS-l" : 1,
  "TS-c" : 1
}

# table to collect measurements
allinfo = {}

while True:
  try:
    line = input() # header
    line2 = input() # time
  except EOFError:
    break

  try:
    _ = input() # blank (not present for last case)
  except EOFError:
    pass

  # parse it
  info = re.findall("==> ./benchmark-(\d*)/usecase_\w*/(.*)/"+sys.argv[1]+"-(\w*).log", line)
  time = re.findall("Execution Time: ([0-9.]*)s", line2)
  print(len(info))

  if len(info) > 0 and len(time) > 0:
    info = info[0]
    time = time[0]

    # NOTE trim "full"
    if info[2].endswith("full"):
      info = (info[0], info[1], info[2][:-4])

    # stick it in the table
    allinfo[info[1]] = allinfo.get(info[1], {})
    allinfo[info[1]][info[2]] = allinfo[info[1]].get(info[2], []) + [float(time)]

# print a CSV
def show_csv():
  for test in tests:
    for arch in archs:
      testname = testnames[test]
      archname = archnames[arch]
      if testname in allinfo and archname in allinfo[testname]:
        times = allinfo[testname][archname]
        print(test + "," + arch + "," + str(sum(times) / len(times)))

def sig_figs(x, n):
  # from stackoverflow
  return round(x, -int(math.floor(math.log10(x))) + (n - 1))

# print a TeX table
def show_tex(which_tests):
  # header
  print("\\begin{tabular}{c|" + ("r@{.}l@{\\,}l" * len(which_tests)) + "}")

  for test in which_tests:
    print(" & \\multicolumn{3}{c}{" + test + "}", end="")

  print(" \\\\ \\hline")

  for arch in archs:
    print(arch, end="")

    for test in which_tests:
      testname = testnames[test]
      archname = archnames[arch]
      if testname in allinfo and archname in allinfo[testname]:
        times = allinfo[testname][archname]
        time = sum(times) / len(times)
        if time < 1:
          print(" & 0 & %d" % int(time * 100 + 0.5), end="")
        elif time < 10:
          ipart = int(time)
          dpart = time - int(time)
          print(" & %d & %d" % (ipart, int(dpart * 10 + 0.5)), end="")
        elif time < 100:
          print(" & %d &" % int(time + 0.5), end="")
        elif time < 1000:
          print(" & %d &" % (int(time / 10. + 0.5) * 10), end="")
        elif time < 10000:
          print(" & %d &" % (int(time / 100. + 0.5) * 100), end="")
        else:
          exit(0)
        print(" & (%d)" % lengths[arch][test], end="")
      else:
        print(" & \\multicolumn{3}{c}{---}", end="")

    print(" \\\\")

  print("\\end{tabular}")

show_csv()
tests = [
  "IS", "GD", "CD", "CL", "CH", "SA",
  "SJ", "LJ", "CRT-i", "CRT-s", "SYS", "IRQ", "TS", "TS-e", "TS-s", "TS-l", "TS-c"
]
show_tex(["IS", "GD", "CD", "CL", "CH"])
show_tex(["SA", "SJ", "LJ", "CRT-i", "CRT-s", "SYS"])
show_tex(["IRQ", "TS", "TS-e", "TS-s", "TS-l", "TS-c"])
