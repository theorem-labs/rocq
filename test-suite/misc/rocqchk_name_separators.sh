#!/usr/bin/env bash

# rocqchk refuses a label that holds a separator that Python's str.splitlines
# breaks at, other than a line feed, or a blank. LabelJ declares
# zqxbadQQQzqxforged; QQQ is rewritten in the library segment of LabelJ.vo,
# at the same length, so that the separator comes just before zqxforged.
# LabelJ is checked (-norec). The load must refuse each name.

. misc/rocqchk_names/lib.sh

compile_plain "$d/base" LabelJ

# jsep LABEL TO: QQQ becomes TO (three bytes).
jsep () {
  cp -r "$d/base" "$d/$1"
  ocaml "$R" "$d/$1/LabelJ.vo" library QQQ "$2"
  both_vm "j-$1" refuse 'has the label "zqxbad' zqxforged -o -Q "$d/$1" BadNames -norec BadNames.LabelJ
}

jsep VT       $'QQ\x0b'           # vertical tab
jsep FF       $'QQ\x0c'           # form feed
jsep FS       $'QQ\x1c'           # file separator
jsep GS       $'QQ\x1d'           # group separator
jsep RS       $'QQ\x1e'           # record separator
jsep NEL      $'Q\xc2\x85'        # U+0085, next line, in UTF-8
jsep NELbyte  $'QQ\x85'           # the byte 0x85 alone: U+0085 in Latin-1
jsep LS       $'\xe2\x80\xa8'     # U+2028, line separator
jsep PS       $'\xe2\x80\xa9'     # U+2029, paragraph separator
jsep CR       $'QQ\r'             # carriage return
jsep SPACE    'QQ '               # a blank: not a line break, but not an identifier
jsep TAB      $'QQ\t'             # a tab: likewise
exit $status
