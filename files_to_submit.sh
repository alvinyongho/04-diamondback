#!/bin/sh

ASGN=03
COMPILER=cobra
EXT=cobra

PREFIX=../$ASGN-$COMPILER

# leave the .git and .stack-work folder and temporary files

find $PREFIX \
  -regextype posix-extended \
  -type f \
  -a ! \( -regex "^${PREFIX}/\.git/.*" -o -regex "^${PREFIX}/\.stack-work/.*" \) \
  -a ! -regex '.*\.(o|s|dSYM|run|log|result)$'
