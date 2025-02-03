#!/usr/bin/env python3

import sys

def remove_marker(filename):
  lines = open(filename, 'r').readlines()
  new_lines = []

  flag = False
  for line in lines:
    if '// {{{' in line:
      flag = True
      continue
    if '// }}}' in line:
      flag = False
      continue

    if not flag:
      new_lines.append(line)
  return ''.join(new_lines)

if __name__ == '__main__':
  print(remove_marker(sys.argv[1]))